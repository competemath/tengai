"""How an angel's `claude` process is confined, as pure functions (nothing here spawns anything).

The same ideas as compete-math's public/leak-containment.mjs: the tool set is pinned (and the test checks the argv a run would get, the way
TauCetiReview checks its reviewer's), the environment is scrubbed of anything that looks like a secret, the working directory is a throwaway
copy and not the repository, and there is no network tool at all. An angel cannot write: it reads a copy of the tree and answers with one JSON
block; the archangel (this program) decides what lands, after the gate. What cannot run cannot be talked into running.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field

READ_TOOLS = ("Read", "Grep", "Glob")
# Everything that writes, runs code, reaches the network or starts another agent is named and refused, whatever the CLI's defaults are.
BANNED_TOOLS = (
    "Bash",
    "Write",
    "Edit",
    "NotebookEdit",
    "Task",
    "Agent",
    "WebSearch",
    "WebFetch",
    "TodoWrite",
    "KillShell",
    "BashOutput",
)
SECRET_NAME = re.compile(r"(TOKEN|SECRET|PASSW|CREDENTIAL|PRIVATE|API_?KEY|ACCESS_?KEY|SESSION_KEY|COOKIE|BRIDGE)", re.I)
CLI_OWN = re.compile(r"^(ANTHROPIC_|CLAUDE_CODE_)")
PASS_THROUGH = ("PATH", "HOME", "LANG", "LC_ALL", "TERM", "TMPDIR", "SHELL", "USER", "LOGNAME")


@dataclass(frozen=True)
class Plan:
    flags: list[str]
    tools: list[str]
    disallowed: list[str]
    settings: dict
    note: str = ""
    allowed: list[str] = field(default_factory=list)


def scrubbed_env(env: dict[str, str]) -> dict[str, str]:
    """The CLI's own credentials are kept (it cannot sign in without them); every other variable that looks like a secret is dropped, and so
    is everything that is not on a short list of harmless basics. The angel has no tool that can print its environment, so this is a second
    lock, not the first."""
    out = {}
    for k, v in env.items():
        if CLI_OWN.match(k):
            out[k] = v
        elif k in PASS_THROUGH and not SECRET_NAME.search(k):
            out[k] = v
    return out


def plan(workdir: str, extra_read_dirs: list[str] | None = None, has_restricted: bool = True) -> Plan:
    if not workdir.startswith("/"):
        raise ValueError("containment needs the angel's own absolute working directory")
    dirs = [workdir, *(extra_read_dirs or [])]
    for d in dirs:
        if not d.startswith("/") or ".." in d.split("/"):
            raise ValueError(f"not an absolute, normalised directory: {d!r}")
    settings = {"autoMemoryEnabled": False}
    if has_restricted:
        tools = list(READ_TOOLS)
        allowed = list(READ_TOOLS)
        flags = ["--restricted", "--tools", *tools, "--allowedTools", *allowed]
        note = "You can Read, Grep and Glob inside your working directory and the directories you were told about. You cannot write or run anything."
    else:
        # An older CLI has no --restricted: Read is allowed only inside the named directories (the path rule "//" starts an absolute path), and
        # everything else is refused by dontAsk. Grep and Glob cannot be scoped by a path rule there, so they are not offered.
        tools = ["Read"]
        allowed = [f"Read(/{d}/**)" for d in dirs]
        flags = ["--permission-mode", "dontAsk", "--tools", *tools, "--allowedTools", *allowed]
        note = "You can Read files inside your working directory and the directories you were told about. You cannot search, write or run anything."
    for d in extra_read_dirs or []:
        flags += ["--add-dir", d]
    return Plan(flags=flags, tools=tools, disallowed=list(BANNED_TOOLS), settings=settings, note=note, allowed=allowed)


def argv(binary: str, model: str, usd: float, p: Plan, system: str = "") -> list[str]:
    """The whole command line. The prompt travels on stdin, never in argv (a long prompt is not a flag, and `ps` does not show it)."""
    cmd = [
        binary,
        "-p",
        "--output-format",
        "json",
        "--no-session-persistence",
        "--model",
        model,
        "--max-budget-usd",
        f"{max(usd, 0.01):.2f}",
        *p.flags,
        "--disallowedTools",
        *p.disallowed,
        "--settings",
        json.dumps(p.settings, separators=(",", ":")),
    ]
    if system:
        cmd += ["--append-system-prompt", system]
    return cmd
