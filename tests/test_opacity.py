import DESops as d
from tests.util import load_model

joint_k_step_methods = ["mapping", "language", "state", "unified"]
separate_k_step_methods = ["mapping", "language", "unified"]


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


def test_joint_k_step_opacity_1():
    g = load_model("models/opacity1.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[1, 5]["secret"] = True

    for method in joint_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 1, method=method) is True
        assert d.opacity.verify_k_step_opacity(g, 2, method=method) is False

    for method in separate_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, joint=False, method=method) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    for method in joint_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 0, method=method) is False

    for method in separate_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, joint=False, method=method) is True


def test_joint_k_step_opacity_2():
    g = load_model("models/opacity2.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[3]["secret"] = True

    for method in joint_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, method=method) is True
        assert d.opacity.verify_k_step_opacity(g, 3, method=method) is False

    for method in separate_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, joint=False, method=method) is True
        assert (
            d.opacity.verify_k_step_opacity(g, 3, joint=False, method=method) is False
        )


def test_joint_k_step_opacity_3():
    g = load_model("models/opacity3.fsm")

    g.vs["init"] = False
    g.vs[0, 3]["init"] = True
    g.vs["secret"] = False
    g.vs[0, 1, 4]["secret"] = True

    for method in joint_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 0, method=method) is True
        assert d.opacity.verify_k_step_opacity(g, 1, method=method) is False

    for method in separate_k_step_methods:
        assert d.opacity.verify_k_step_opacity(g, 1, joint=False, method=method) is True
        assert (
            d.opacity.verify_k_step_opacity(g, 2, joint=False, method=method) is False
        )


def test_joint_infinite_step_opacity():
    g = load_model("models/opacity4.fsm")

    g.vs["init"] = True
    g.vs["secret"] = False
    g.vs[2]["secret"] = True

    assert d.opacity.verify_infinite_step_opacity(g) is True

    g.vs["secret"] = False
    g.vs[4]["secret"] = True

    assert d.opacity.verify_infinite_step_opacity(g) is False
