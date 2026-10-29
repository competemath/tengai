import pytest

from anomalous_archangel import containment
from anomalous_archangel.agents import AgentSpec, ClaudeCliRunner


def spec(**kw):
    base = {"lens": "abstractor", "prompt": "SECRET-PROMPT-TEXT", "system": "sys", "model": "m", "usd": 1.234, "workdir": "/work/a"}
    return AgentSpec(**{**base, **kw})


def test_the_argv_a_run_would_get_spawns_nothing_and_pins_the_tools():
    r = ClaudeCliRunner("claude", env={}, has_restricted=True)
    cmd = r.argv(spec(extra_read_dirs=["/t/Tengoku"]))
    assert cmd[0] == "claude" and "-p" in cmd
    tools = cmd[cmd.index("--tools") + 1 : cmd.index("--allowedTools")]
    assert tools == ["Read", "Grep", "Glob"]
    banned = cmd[cmd.index("--disallowedTools") + 1 : cmd.index("--settings")]
    for t in ("Bash", "Write", "Edit", "WebFetch", "WebSearch", "Task", "Agent"):
        assert t in banned
    assert "--restricted" in cmd and "--no-session-persistence" in cmd
    assert cmd[cmd.index("--max-budget-usd") + 1] == "1.23"
    assert "SECRET-PROMPT-TEXT" not in " ".join(cmd)  # the prompt travels on stdin
    assert "--dangerously-skip-permissions" not in cmd
    assert cmd.count("--add-dir") == 1


def test_an_older_cli_without_restricted_gets_path_scoped_read_only():
    cmd = ClaudeCliRunner("claude", env={}, has_restricted=False).argv(spec(extra_read_dirs=["/t/Tengoku"]))
    assert "--restricted" not in cmd
    assert cmd[cmd.index("--permission-mode") + 1] == "dontAsk"
    assert cmd[cmd.index("--tools") + 1 : cmd.index("--allowedTools")] == ["Read"]
    allowed = cmd[cmd.index("--allowedTools") + 1 : cmd.index("--add-dir")]
    assert allowed == ["Read(//work/a/**)", "Read(//t/Tengoku/**)"]


def test_relative_or_escaping_directories_are_refused():
    with pytest.raises(ValueError):
        containment.plan("work")
    with pytest.raises(ValueError):
        containment.plan("/work", ["/a/../etc"])


def test_the_environment_keeps_the_cli_login_and_drops_secrets():
    env = {
        "PATH": "/bin",
        "HOME": "/h",
        "CLAUDE_CODE_OAUTH_TOKEN": "keep",
        "ANTHROPIC_API_KEY": "keep too",
        "GH_TOKEN": "x",
        "GITHUB_TOKEN": "x",
        "AWS_SECRET_ACCESS_KEY": "x",
        "BRIDGE_TOKEN": "x",
        "RANDOM_THING": "x",
    }
    out = containment.scrubbed_env(env)
    assert set(out) == {"PATH", "HOME", "CLAUDE_CODE_OAUTH_TOKEN", "ANTHROPIC_API_KEY"}
