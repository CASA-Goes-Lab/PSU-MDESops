import DESops as d
from DESops.opacity.opacity_verification_language_based import (
    verify_joint_k_step_opacity_language_based,
)

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
Euo = g.Euo

secret_states = [1, 5]
g.vs["secret"] = False
g.vs[secret_states]["secret"] = True

print(verify_joint_k_step_opacity_language_based(g, 1))  # True
print(verify_joint_k_step_opacity_language_based(g, 2))  # False
print()

secret_states = [2, 4]
g.vs["secret"] = False
g.vs[secret_states]["secret"] = True

print(verify_joint_k_step_opacity_language_based(g, 1))  # False
print(verify_joint_k_step_opacity_language_based(g, 2))  # False
print()

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
Euo = g.Euo

secret_states = [0]
g.vs["secret"] = False
g.vs[secret_states]["secret"] = True

print(verify_joint_k_step_opacity_language_based(g, 1))  # True
print(verify_joint_k_step_opacity_language_based(g, 2))  # False
