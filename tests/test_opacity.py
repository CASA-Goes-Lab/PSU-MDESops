import DESops as d
from tests.util import load_model

# methods for k-step opacity
k_joint_methods = ["language", "state", "trajectory"]
k_separate_methods = k_joint_methods + ["TWO"]

# methods for infinite-step opacity
infinite_joint_methods = ["language", "state"]
infinite_separate_methods = ["TWO"]


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


def test_initial_state_opacity():
    g = load_model("models/textbook/fig_2-42.fsm")
    g.vs["init"] = True

    g.vs["secret"] = False
    g.vs[3, 4]["secret"] = True
    assert d.opacity.verify_initial_state_opacity(g) is True

    g.vs["secret"] = False
    g.vs[1, 2]["secret"] = True
    assert d.opacity.verify_initial_state_opacity(g) is False


def test_k_step_opacity_1():
    g = load_model("models/opacity1.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[1, 5]["secret"] = True

    for m in k_joint_methods:
        assert d.opacity.verify_k_step_opacity(g, 1, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, True, 1, m) is False

        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is True

    for m in k_separate_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is True

        assert d.opacity.verify_k_step_opacity(g, 2, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    for m in k_joint_methods:
        assert d.opacity.verify_k_step_opacity(g, 0, True, 1, m) is False

        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is True

    for m in k_separate_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is True

        assert d.opacity.verify_k_step_opacity(g, 0, False, 1, m) is False


def test_k_step_opacity_2():
    g = load_model("models/opacity2.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[3]["secret"] = True

    for m in k_joint_methods:
        assert d.opacity.verify_k_step_opacity(g, 2, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 3, True, 1, m) is False

        assert d.opacity.verify_k_step_opacity(g, 3, True, 2, m) is True

    for m in k_separate_methods:
        assert d.opacity.verify_k_step_opacity(g, 3, False, 2, m) is True

        assert d.opacity.verify_k_step_opacity(g, 2, False, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 3, False, 1, m) is False


def test_k_step_opacity_3():
    g = load_model("models/opacity3.fsm")

    g.vs["init"] = False
    g.vs[0, 3]["init"] = True
    g.vs["secret"] = False
    g.vs[0, 1, 4]["secret"] = True

    for m in k_joint_methods:
        assert d.opacity.verify_k_step_opacity(g, 0, True, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 1, True, 1, m) is False

        assert d.opacity.verify_k_step_opacity(g, 1, True, 2, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, True, 2, m) is False

    for m in k_separate_methods:
        assert d.opacity.verify_k_step_opacity(g, 1, False, 2, m) is True
        assert d.opacity.verify_k_step_opacity(g, 2, False, 2, m) is False

        assert d.opacity.verify_k_step_opacity(g, 0, False, 1, m) is True
        assert d.opacity.verify_k_step_opacity(g, 1, False, 1, m) is False


def test_infinite_step_opacity():
    g = load_model("models/opacity4.fsm")

    g.vs["init"] = True
    g.vs["secret"] = False
    g.vs[1]["secret"] = True

    for m in infinite_joint_methods:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is True

    for m in infinite_separate_methods:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2]["secret"] = True

    for m in infinite_joint_methods:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is True

    for m in infinite_separate_methods:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    for m in infinite_joint_methods:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in infinite_separate_methods:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is True

    g.vs["secret"] = False
    g.vs[2, 3]["secret"] = True

    for m in infinite_joint_methods:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in infinite_separate_methods:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is True
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is False

    g.vs["secret"] = False
    g.vs[2, 3, 4]["secret"] = True

    for m in infinite_joint_methods:
        assert d.opacity.verify_infinite_step_opacity(g, True, 1, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, True, 2, m) is False

    for m in infinite_separate_methods:
        assert d.opacity.verify_infinite_step_opacity(g, False, 2, m) is False
        assert d.opacity.verify_infinite_step_opacity(g, False, 1, m) is False


def test_k_step_num_states():
    i = 4
    K = 3

    g = d.NFA()
    g.add_vertices(i)
    g.vs["init"] = True
    g.vs["secret"] = False
    g.vs[0]["secret"] = True

    for j in range(i):
        for k in range(i):
            g.add_edge(j, k, str(k))
    g.generate_out()

    _, num_states = d.opacity.verify_k_step_opacity(
        g, K, method="trajectory", return_num_states=True
    )
    assert num_states == (i ** (K + 2) - 1) / (i - 1)
