import json

import pytest

from anomalous_archangel import proposals


def wrap(d):
    return "thinking...\n\n```json\n" + json.dumps(d) + "\n```\n"


GOOD = {
    "summary": "s",
    "findings": [{"kind": "bridge", "label": "conjecture", "title": "t", "body": "b", "refs": ["Tengai.x"]}],
    "lean_files": [{"path": "Tengai/A/B.lean", "content": "import Tengoku.All\n", "purpose": "p"}],
    "requests": [{"statement": "∀ n : ℕ, n = n", "informal": "i", "why": "w"}],
    "delegate": [{"lens": "bridger", "brief": "look"}],
}


def test_a_good_answer_parses():
    p = proposals.parse(wrap(GOOD))
    assert p.findings[0]["label"] == "conjecture" and p.lean_files[0]["path"] == "Tengai/A/B.lean" and len(p.delegate) == 1


def test_only_the_last_block_counts():
    assert proposals.parse(wrap({"summary": "old"}) + wrap({"summary": "new"})).summary == "new"


def test_helpers_cannot_delegate():
    assert proposals.parse(wrap(GOOD), allow_delegate=False).delegate == []


@pytest.mark.parametrize(
    "mutate",
    [
        lambda d: d["findings"][0].update(label="verified"),
        lambda d: d["findings"][0].update(kind="proof"),
        lambda d: d["lean_files"][0].update(path="../Tengai/A.lean"),
        lambda d: d["lean_files"][0].update(path="Tengoku/A.lean"),
        lambda d: d["findings"][0].update(body="x" * 5000),
        lambda d: d.update(extra=1),
        lambda d: d["findings"][0].update(surprise=1),
        lambda d: d.update(findings=[GOOD["findings"][0]] * 9),
        lambda d: d["requests"][0].update(statement=""),
    ],
)
def test_bad_answers_are_refused(mutate):
    d = json.loads(json.dumps(GOOD))
    mutate(d)
    with pytest.raises(proposals.BadProposal):
        proposals.parse(wrap(d))


def test_no_block_and_broken_json():
    with pytest.raises(proposals.BadProposal):
        proposals.parse("just prose")
    with pytest.raises(proposals.BadProposal):
        proposals.parse("```json\n{nope\n```")
