import DESops as d
from DESops.opacity.opacity_verification_alternative import (
    verify_joint_infinite_step_opacity_alternative,
    verify_joint_k_step_opacity_alternative,
)


def test_joint_k_step_opacity_alternative():
    g = d.Automata()
    g.add_vertices(6, range(6))
    g.add_edges(
        [(0, 1), (1, 2), (2, 3), (0, 4), (4, 5), (5, 3)],
        labels=["u", "a", "a", "a", "u", "a"],
    )

    g.vs["init"] = False
    g.vs[0]["init"] = True

    Eo = ["a"]
    g.es["obs"] = False
    g.es.select(label_in=Eo)["obs"] = True
    g.find_Euc_Euo()

    secret_states = [1, 5]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_k_step_opacity_alternative(g, 1) is True
    assert verify_joint_k_step_opacity_alternative(g, 2) is False

    secret_states = [2, 4]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_k_step_opacity_alternative(g, 1) is False
    assert verify_joint_k_step_opacity_alternative(g, 2) is False

    g = d.Automata()
    g.add_vertices(5, range(5))
    g.add_edges(
        [(0, 1), (0, 3), (0, 2), (1, 4), (2, 2), (3, 4), (4, 4)],
        labels=["b", "a", "u", "b", "a", "b", "a"],
    )

    g.vs["init"] = True

    Eo = ["a", "b"]
    g.es["obs"] = False
    g.es.select(label_in=Eo)["obs"] = True
    g.find_Euc_Euo()

    secret_states = [0]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_k_step_opacity_alternative(g, 1) is True
    assert verify_joint_k_step_opacity_alternative(g, 2) is False

    g = d.Automata()
    g.add_vertices(2)
    g.add_edges([(0, 0), (0, 1)], labels=["u", "u"])

    g.vs["init"] = False
    g.vs[0]["init"] = True

    g.es["obs"] = False
    g.find_Euc_Euo()

    secret_states = [0]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_k_step_opacity_alternative(g, 0) is False


def test_joint_infinite_step_opacity_alternative():
    g = d.Automata()
    g.add_vertices(5, range(5))
    g.add_edges(
        [(0, 1), (0, 3), (0, 2), (1, 4), (2, 2), (3, 4), (4, 4)],
        labels=["b", "a", "u", "b", "a", "b", "a"],
    )

    g.vs["init"] = True

    Eo = ["a", "b"]
    g.es["obs"] = False
    g.es.select(label_in=Eo)["obs"] = True
    g.find_Euc_Euo()

    secret_states = [2]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_infinite_step_opacity_alternative(g) is True

    secret_states = [4]
    g.vs["secret"] = False
    g.vs[secret_states]["secret"] = True

    assert verify_joint_infinite_step_opacity_alternative(g) is False
