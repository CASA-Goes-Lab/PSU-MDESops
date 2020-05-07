import itertools
import os
import subprocess
from pathlib import Path

import igraph as ig


def construct_explicit_AES(arena, G, E, Euc, Euo, X_crit, debug=False):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata, igraph graph object
    # E: set of events of G
    # Euc: set of uncontrollable events of G
    # Euc: set of unobservable events of G
    # X_crit: safety specification
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False
    if debug:
        import time

        start_time = time.process_time()
    Eo = E - Euo


#     A1 = set()
#     # find_A1_sets(A1, G, Euc)
#     singleton_A1_set(A1,G,E,Euc)
#     print(A1)
#     Ea_e = find_Ea_e_events(G, E, Ea)
#     A2 = Ea_e | Eo
#     queue = list()
#     init_state = (frozenset({0}))
#     queue.append(init_state)
#     Q1, Q2, h1, h2 = set(), set(), list(), list()
#     Q1.add(init_state)
#     adj_dict = dict()

#     search_opt(G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug)
#     # print(adj_dict)
#     # print(Q1)
#     # print(len(Q2))
#     convert_to_graph_opt(arena, G, Q1, Q2, h1, h2, init_state,adj_dict)
#     Euc_new = {e.name() for e in Ea_e}
#     Euc_new = Euc_new.union(E)
#     Euc_new.add(frozenset(Euc))
#     Euo_new = {e.name() for e in Ea_e}
#     if debug:
#         print("-----")
#         print("Final Vcount: {0}".format(str(arena.vcount())))
#         print("Time elapsed: {0}".format(str(time.process_time() - start_time)))
#         print("-----")

#     return [Euc_new, Euo_new]

# def search_opt(G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug):
#     X_crit = set([v.index for v in G.vs.select(name_in = X_crit)])

#     while queue:
#         # print(len(queue))
#         q = queue.pop(0)
#         if Q1_state_opt(q):
#             # Q1 to Q2 transitions
#             # events = gamma_feasible(G, q, Euc)
#             events = A1
#             adj = list()
#             for e in events:
#                 target = (UR(q, G, e, Euo), frozenset(e), None)
#                 h1.append((q, e, target))
#                 adj.append((target,e))
#                 add_to_arena_opt(Q1,Q2,target,queue, X_crit,adj_dict, debug)
#             adj_dict[q] = adj
#         elif Q2_state_opt(q):
#             # Various types of Q2 transitions
#             # print(q)
#             # print(type(q))
#             adj = list()
#             for e in A2:
#                 if q[2] == e and e in Ea:
#                     # 2nd type, Q2->Q1
#                     target = (q[0])
#                     h2.append((q,e,target))
#                     add_to_arena_opt(Q1,Q2,target,queue, X_crit,adj_dict, debug)
#                     adj.append((target,e))
#                 if q[2] == None:
#                     if e in Eo and e in G.es(_source_in = q[0])["label"] and e in q[1]:
#                         # 1st type, Q2->Q1
#                         target = (NX(e,q[0],G))
#                         h2.append((q,e,target))
#                         add_to_arena_opt(Q1,Q2,target,queue, X_crit,adj_dict, debug)
#                         adj.append((target,e))
#                     if isinstance(e, Event) and e.inserted and e.label in q[1]:
#                         # 3rd type, Q2->Q2
#                         # print('_'.join(e.name()))
#                         target = (q[0], q[1], M(e))
#                         h2.append((q,e.name(),target))
#                         add_to_arena_opt(Q1,Q2,target,queue, X_crit,adj_dict,debug)
#                         adj.append((target,e.name()))
#                     if isinstance(e, Event) and e.deleted and e.label in G.es(_source_in = q[0])["label"] and e.label in q[1]:
#                         # 4th type, Q2->Q2
#                         # proj is just M(e) since e is in Ead (not in Eai)
#                         target = (UR(NX(e.label,q[0],G),G,q[1],Euo), q[1], None)
#                         # if target[0] == frozenset():
#                             # print(q[1])
#                             # print(UR(frozenset({3}),G,q[1],Euo))
#                             # print(e.label)
#                         h2.append((q,e.name(),target))
#                         add_to_arena_opt(Q1,Q2,target,queue, X_crit,adj_dict, debug)
#                         adj.append((target,e.name()))
#             # print(q)
#             adj_dict[q] = adj

# def convert_to_graph_opt(arena, G, Q1, Q2, h1, h2, init_state,adj_dict):
#     # Convert Q1, Q2 states and h1, h2 edges to arena, an igraph Graph
#     arena.add_vertices(len(Q1)+len(Q2))
#     # [print(key, value) for key, value in adj_dict.items()]
#     Q1.remove(init_state)
#     V_names = list()
#     V_names.append("{"+G.vs["name"][0]+"}")
#     E_list = list()
#     E_events = list()
#     # Convert Q1 and Q2 into a dict with name : index
#     adj_list = list()
#     Q_dict = dict()
#     Q_dict[init_state] = 0
#     Q = list()
#     for i,q in enumerate(Q1,1):
#         q0_names = "{"+','.join([G.vs["name"][l] for l in q])+"}"
#         t = (q0_names)
#         V_names.append(t)
#         Q_dict[q] = i
#         Q.append(q)
#     for j,q in enumerate(Q2,i+1):
#         q0_names = "{"+','.join([G.vs["name"][l] for l in q[0]])+"}"
#         q1 = "{"+ ','.join({u for u in q[1]}) + "}"
#         t = "("+ ','.join([q0_names, q1, str(q[2])])+ ")"
#         V_names.append(t)
#         Q_dict[q] = j
#         Q.append(q)

#     adj_list.append([(Q_dict[v[0]],v[1]) for v in adj_dict[init_state]])
#     adj_list.extend([[(Q_dict[v[0]],v[1]) for v in adj_dict[Q[i]]] for i,x in enumerate(Q)])
#     # print(adj_list)
#     # [print(key, value) for key, value in Q_dict.items()]
#     # print(V_names)
#     # print(len(Q1)+len(Q2))

#     for h in h1:
#         source = Q_dict[h[0]]
#         target = Q_dict[h[2]]
#         E_list.append((source,target))
#         E_events.append(h[1])
#     for h in h2:
#         source = Q_dict[h[0]]
#         target = Q_dict[h[2]]
#         E_list.append((source,target))
#         E_events.append(h[1])

#     # print(V_names)
#     arena.vs["name"] = V_names
#     arena.add_edges(E_list)
#     arena.es["label"] = E_events
#     arena.vs["adj"] = adj_list
