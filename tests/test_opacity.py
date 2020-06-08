from DESops.opacity.opacity_verification import (
    verify_joint_k_step_opacity,
    verify_separate_k_step_opacity,
)
from DESops.opacity.opacity_verification_alternative import (
    verify_joint_infinite_step_opacity_alternative,
    verify_joint_k_step_opacity_alternative,
    verify_separate_k_step_opacity_alternative,
)
from tests.util import load_model


def test_joint_k_step_opacity_1():
    g = load_model("models/opacity1.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[1, 5]["secret"] = True

    assert verify_joint_k_step_opacity(g, 1) is True
    assert verify_joint_k_step_opacity(g, 2) is False
    assert verify_joint_k_step_opacity_alternative(g, 1) is True
    assert verify_joint_k_step_opacity_alternative(g, 2) is False
    assert verify_separate_k_step_opacity(g, 2) is True
    assert verify_separate_k_step_opacity_alternative(g, 2) is True

    g.vs["secret"] = False
    g.vs[2, 4]["secret"] = True

    assert verify_joint_k_step_opacity(g, 0) is False
    assert verify_joint_k_step_opacity_alternative(g, 0) is False
    assert verify_separate_k_step_opacity(g, 2) is True
    assert verify_separate_k_step_opacity_alternative(g, 2) is True


def test_joint_k_step_opacity_2():
    g = load_model("models/opacity2.fsm")

    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[3]["secret"] = True

    assert verify_joint_k_step_opacity(g, 2) is True
    assert verify_joint_k_step_opacity(g, 3) is False
    assert verify_joint_k_step_opacity_alternative(g, 2) is True
    assert verify_joint_k_step_opacity_alternative(g, 3) is False

    assert verify_separate_k_step_opacity(g, 2) is True
    assert verify_separate_k_step_opacity(g, 3) is False
    assert verify_separate_k_step_opacity_alternative(g, 2) is True
    assert verify_separate_k_step_opacity_alternative(g, 3) is False


def test_joint_k_step_opacity_3():
    g = load_model("models/opacity3.fsm")

    g.vs["init"] = False
    g.vs[0, 3]["init"] = True
    g.vs["secret"] = False
    g.vs[0, 1, 4]["secret"] = True

    assert verify_joint_k_step_opacity(g, 0) is True
    assert verify_joint_k_step_opacity(g, 1) is False
    assert verify_joint_k_step_opacity_alternative(g, 0) is True
    assert verify_joint_k_step_opacity_alternative(g, 1) is False

    assert verify_separate_k_step_opacity(g, 1) is True
    assert verify_separate_k_step_opacity(g, 2) is False
    assert verify_separate_k_step_opacity_alternative(g, 1) is True
    assert verify_separate_k_step_opacity_alternative(g, 2) is False


def test_joint_infinite_step_opacity():
    g = load_model("models/opacity4.fsm")

    g.vs["init"] = True
    g.vs["secret"] = False
    g.vs[2]["secret"] = True

    assert verify_joint_infinite_step_opacity_alternative(g) is True

    g.vs["secret"] = False
    g.vs[4]["secret"] = True

    assert verify_joint_infinite_step_opacity_alternative(g) is False
