"""The conventions Tengoku's own gate enforces on workflows, enforced here too: pinned actions, no ambient permissions, no stored credentials,
no free text in `run:`."""

import re
from pathlib import Path

import pytest

WF = sorted((Path(__file__).resolve().parent.parent / ".github" / "workflows").glob("*.yml"))
PINNED = re.compile(r"^\s*-?\s*uses:\s*[\w./-]+@[0-9a-f]{40}\s+#\s*\S+")


@pytest.mark.parametrize("path", WF, ids=lambda p: p.name)
def test_workflow_is_yaml(path):
    yaml = pytest.importorskip("yaml")
    assert isinstance(yaml.safe_load(path.read_text()), dict)


@pytest.mark.parametrize("path", WF, ids=lambda p: p.name)
def test_workflow_conventions(path):
    lines = path.read_text().splitlines()
    text = "\n".join(lines)
    assert re.search(r"(?m)^permissions: \{\}\s*$", text), "top-level permissions: {}"
    for i, ln in enumerate(lines):
        if re.match(r"^\s*-?\s*uses:", ln):
            assert PINNED.match(ln), f"line {i + 1}: pin to a 40-character SHA with the tag as a comment"
            if "actions/checkout@" in ln:
                assert "persist-credentials: false" in " ".join(lines[i : i + 4]), f"line {i + 1}: checkout must drop its token"
    in_run = False
    indent = 0
    for i, ln in enumerate(lines):
        m = re.match(r"^(\s*)(-\s+)?run:\s*(\|.*|>.*)?(.*)$", ln)
        if m:
            indent = len(m.group(1)) + (len(m.group(2) or ""))
            in_run = True
            body = m.group(4) or ""
            assert "${{" not in body, f"line {i + 1}: no ${{{{ }}}} in run:"
            continue
        if in_run:
            if ln.strip() and (len(ln) - len(ln.lstrip())) <= indent:
                in_run = False
            else:
                assert "${{" not in ln, f"line {i + 1}: move the expression into env: and use the shell variable"
