"""Running an angel: the real `claude` CLI under containment, or a deterministic fake for tests and --dry-run."""

from __future__ import annotations

import json
import os
import subprocess
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path

from . import containment


@dataclass
class AgentSpec:
    lens: str
    prompt: str
    system: str
    model: str
    usd: float
    workdir: str
    timeout_s: int = 900
    extra_read_dirs: list[str] = field(default_factory=list)


@dataclass
class AgentResult:
    ok: bool
    text: str
    cost_usd: float = 0.0
    turns: int = 0
    error: str = ""


class ClaudeCliRunner:
    def __init__(self, binary: str = "claude", env: dict[str, str] | None = None, has_restricted: bool | None = None) -> None:
        self.binary = binary
        self.env = containment.scrubbed_env(dict(os.environ if env is None else env))
        self.has_restricted = self._probe() if has_restricted is None else has_restricted

    def _probe(self) -> bool:
        """Does the installed CLI know --restricted? Asked of its own help text; an unreadable help means a current CLI."""
        try:
            r = subprocess.run([self.binary, "--help"], capture_output=True, text=True, timeout=30, env=self.env, check=False)
            text = r.stdout + r.stderr
            return "--restricted" in text if "--permission-mode" in text else True
        except (OSError, subprocess.SubprocessError):
            return True

    def argv(self, spec: AgentSpec) -> list[str]:
        p = containment.plan(str(Path(spec.workdir).resolve()), [str(Path(d).resolve()) for d in spec.extra_read_dirs], self.has_restricted)
        return containment.argv(self.binary, spec.model, spec.usd, p, f"{spec.system}\n\n{p.note}".strip())

    def run(self, spec: AgentSpec) -> AgentResult:
        try:
            r = subprocess.run(
                self.argv(spec),
                input=spec.prompt,
                capture_output=True,
                text=True,
                timeout=spec.timeout_s,
                cwd=spec.workdir,
                env=self.env,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return AgentResult(False, "", 0.0, 0, f"timed out after {spec.timeout_s} s")
        except OSError as e:
            return AgentResult(False, "", 0.0, 0, f"could not start {self.binary}: {e}")
        try:
            out = json.loads(r.stdout)
        except ValueError:
            return AgentResult(False, r.stdout[-2000:], 0.0, 0, f"unreadable output (exit {r.returncode}): {r.stderr[-300:]}")
        text = str(out.get("result", ""))
        return AgentResult(
            ok=not out.get("is_error", False) and r.returncode == 0,
            text=text,
            cost_usd=float(out.get("total_cost_usd") or 0.0),
            turns=int(out.get("num_turns") or 0),
            error="" if not out.get("is_error") else text[:300],
        )


class FakeRunner:
    """Answers from a function of the spec: no process, no network, no money. The whole pipeline runs on it in the tests and in --dry-run."""

    def __init__(self, answer: Callable[[AgentSpec], str | dict], cost: float = 0.01) -> None:
        self.answer = answer
        self.cost = cost
        self.specs: list[AgentSpec] = []

    def run(self, spec: AgentSpec) -> AgentResult:
        self.specs.append(spec)
        a = self.answer(spec)
        text = a if isinstance(a, str) else "Here is what I found.\n\n```json\n" + json.dumps(a) + "\n```\n"
        return AgentResult(True, text, min(self.cost, spec.usd), 1)
