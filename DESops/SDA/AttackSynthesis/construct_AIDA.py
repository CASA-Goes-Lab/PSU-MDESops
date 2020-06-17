import itertools
import os
import subprocess
import time

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.basic_operations.ureach import ureach_from_set_adj
from DESops.supervisory_control import supr_contr


# Construct-AIDA algorithm
# Requires system G, supervisor Rt (~R), and set of events vulnerable to attacks Ea
# Returns an AIDA-structure graph
# dead_state is the index in h
# Also optionally requires controllable/observable event sets Euc/Euo
def construct_AIDA(G, R, Ea):
    # Set initial states
    x0 = frozenset([0])
    q0 = 0


#     S = True
#     AIDA = AIDA_Class((x0, q0, S))
#     DoBFS(AIDA, G, Rt, (x0, q0, S), X_crit, Ea, Euc, Euo)
#     AIDA.set_dead_state_index(dead_state)
#     return AIDA

# # y:= ({x0}, q0)
# def DoBFS(AIDA, G, Rt, y, X_crit, Ea, Euc, Euo):
#     S = True
#     E = False
#     # Initialization (lines 3,4)
#     AIDA.S.add(y)
#     # Using list data structure for queue Q
#     Q = list()
#     Q.append(y)

#     # While Q is not empty:
#     while Q:
#         c = Q.pop(0)
#         if c in AIDA.S and AIDA.is_S_state(c):
#             # line 8: g = transition function ~R (Is(C))
#             g = active_event_set(Rt, IS(c))
#             z1 = set()
#             ureach_from_set(z1, IG(c), G, Euo.intersection(g["label"])) #Rom: I had to include ["label"] after g since it was returning the empty set
#             z = (frozenset(z1), IS(c), E)
#             AIDA.h.add(((c,z),frozenset(g["label"])))
#             add_state_to_AIDA(z, AIDA, Q, Rt, X_crit, G)

#         elif c in AIDA.E and AIDA.is_E_state(c):
#             for e in active_event_set(Rt, IS(c))["label"]:
#                 if e in Euo:
#                     continue
#                 rho_G_IG = active_event_set(G, IG(c))
#                 if e in rho_G_IG["label"]:
#                     y = (NX(e, IG(c), G), ut(IS(c), e, Rt), S)
#                     pair = (c, y)
#                     AIDA.h.add((pair,e))
#                     add_state_to_AIDA(y, AIDA, Q, Rt, X_crit, G)
#                 if e in rho_G_IG["label"] and e in Ea:
#                     y = (NX(e, IG(c), G), IS(c), S)
#                     pair = (c,y)
#                     # Line 20: e is subscripted ('ed') as a deleted-event in Ea
#                     AIDA.h.add((pair, Event.deleted(e)))
#                     add_state_to_AIDA(y, AIDA, Q, Rt, X_crit, G)
#                 if e in Ea:
#                     y = (IG(c), ut(IS(c), e, Rt), S)
#                     pair = (c,y)
#                     # Line 24: e is subscripted ('ei') as an insertable-event in Ea
#                     AIDA.h.add((pair,Event.inserted(e)))
#                     add_state_to_AIDA(y, AIDA, Q, Rt, X_crit, G)
#     return AIDA

# # Procedure to add states to AIDA & develop queue
# # Requires state c, AIDA structure, queue Q, supervisor Rt, and set of critical states X_crit
# def add_state_to_AIDA(c, AIDA, Q, Rt, X_crit, G):
#     if c not in AIDA.E and AIDA.is_E_state(c):
#         AIDA.E.add(c)
#         # Check if IG(c) is not a subset of X_crit:
#         # Equivalent to there is at least one state in IG(c) that is not a critical state
#         for state in IG(c):
#             if G.vs[state]["name"] not in X_crit:
#                 Q.append(c)
#                 break
#     if c not in AIDA.S and AIDA.is_S_state(c):
#         AIDA.S.add(c)
#         # Check if IS(c) is not dead:
#         # Equivalent to checking if the associated state in Rt is not the dead state ---
#         # which has the index (# of vertices - 1)
#         if IS(c) != Rt.vcount() - 1:
#             Q.append(c)
#     return


# # NX function defined in section 2 of paper:
# # Observable reach (or next set of states)
# # Given event in Eo and a set of states in G (and the graph G)
# # Returns a frozen set of states in X that are reached by event from states in S
# def NX(event, S, G):
#     # Assuming event is in Eo:
#     edges = G.es(_source_in = S)
#     next_states = [e.target for e in edges if e["label"] == event]
#     return frozenset(next_states)

# # transition function for Rt; given a state and event, returns the target
# def ut(state, event, Rt):
#     return Rt.es(_source = state)(label_eq = event)[0].target

# # c is defined as a tuple where c = (IG(c), IS(c))
# # IS(c): the state of the supervisor (corrupted by attacks)
# def IS(c):
#     return c[1]
# # IG(c): the actual estimate of the system's state (given as a set of states in G)
# def IG(c):
#     return c[0]


# # Determines the set of active events at state S, or set of states S
# # where X: states of G
# def active_event_set(G, S):
#     if type(S) == int:
#         return G.es(_source = S)
#     else:
#         return G.es(_source_in = S)
