import DESops as d
from tests.util import load_model

# methods for k-step opacity
k_joint_1 = ["language", "mapping", "state", "state-observer", "unified"]
k_joint_2 = ["language", "mapping", "state-observer", "unified"]
k_separate_2 = ["language", "mapping", "state-observer", "TWO", "unified"]
k_separate_1 = ["language", "mapping", "state-observer", "TWO", "unified"]

# methods for infinite-step opacity
inf_joint = ["language", "unified"]
inf_separate = ["TWO"]


def test_current_state_opacity():
    g = load_model("models/opacity1.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    assert d.opacity.verify_current_state_opacity(g) is True

    g.vs["secret"] = False
    g.vs[3]["secret"] = True

    assert d.opacity.verify_current_state_opacity(g) is False


def test_k_step_opacity_1():
    g = load_model("models/opacity1.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[1, 5]["secret"] = True

    for m in k_joint_1:
        assert d.opacity.verify_k_step_opacity(g, 1, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, True, 1, m) is False

    for m in k_joint_2:
        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is True

    for m in k_separate_2:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is True

    for m in k_separate_1:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    for m in k_joint_1:
        assert d.opacity.verify_k_step_opacity(g, 0, True, 1, m) is False

    for m in k_joint_2:
        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is True

    for m in k_separate_2:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is True

    for m in k_separate_1:
        assert d.opacity.verify_k_step_opacity(g, 0, False, 1, m) is False


def test_k_step_opacity_2():
    g = load_model("models/opacity2.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[3]["secret"] = True

    for m in k_joint_1:
        assert d.opacity.verify_k_step_opacity(g, 2, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 3, True, 1, m) is False

    for m in k_joint_2:
        assert d.opacity.verify_k_step_opacity(g, 3, True, 2, m) is True

    for m in k_separate_2:
        assert d.opacity.verify_k_step_opacity(g, 3, False, 2, m) is True

    for m in k_separate_1:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 3, False, 1, m) is False


def test_k_step_opacity_3():
    g = load_model("models/opacity3.fsm")

    g.vs["init"] = False
    g.vs[0, 3]["init"] = True
    g.vs["secret"] = False
    g.vs[0, 1, 4]["secret"] = True

    for m in k_joint_1:
        assert d.opacity.verify_k_step_opacity(g, 0, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 1, True, 1, m) is False

    for m in k_joint_2:
        assert d.opacity.verify_k_step_opacity(g, 1, True, 2, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is False

    for m in k_separate_2:
        assert d.opacity.verify_k_step_opacity(g, 1, False, 2, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is False

    for m in k_separate_1:
        assert d.opacity.verify_k_step_opacity(g, 0, False, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 1, False, 1, m) is False


def test_infinite_step_opacity():
    g = load_model("models/opacity4.fsm")

    g.vs["init"] = True
    g.vs["secret"] = False
    g.vs[1]["secret"] = True

    for m in inf_joint:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is True

    for m in inf_separate:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2]["secret"] = True

    for m in inf_joint:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is True

    for m in inf_separate:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    for m in inf_joint:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in inf_separate:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 3]["secret"] = True

    for m in inf_joint:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in inf_separate:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is False

    g.vs["secret"] = False
    g.vs[2, 3, 4]["secret"] = True

    for m in inf_joint:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in inf_separate:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is False
