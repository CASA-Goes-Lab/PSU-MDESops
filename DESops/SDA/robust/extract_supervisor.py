import igraph as ig

from DESops.basic.observer_comp import observer_comp as observer
from DESops.basic.parallel_comp import parallel_comp

from .temp_scns import scns


def select_supervisor(arena, Euo, Euc):
    g = arena._graph
    R = ig.Graph(directed=True)
    Q = list()
    trans = list()
    trans_labels = list()
    vertex = list()
    Q.append(0)
    vertex.append(0)
    while Q:
        q = Q.pop(0)
        # print(Q)
        transq1 = [e for e in g.es.select(_source=q)]
        transitions = [e["label"] for e in transq1]
        max_control_action = max(transitions, key=len)
        # print(max_control_action)
        q2 = [e.target for e in transq1 if e["label"] == max_control_action][0]
        for e in max_control_action:
            if e in Euo:
                trans_labels.append(e)
                trans.append((vertex.index(q), vertex.index(q)))
            else:
                # print(e)
                transq2 = [v.target for v in g.es.select(_source=q2) if v["label"] == e]
                # print(transq2)
                if transq2:
                    add_vertex(vertex, Q, transq2[0])
                    trans_labels.append(e)
                    trans.append((vertex.index(q), vertex.index(transq2[0])))

                else:
                    trans_labels.append(e)
                    trans.append((vertex.index(q), vertex.index(q)))

    # Construct graph
    # print(vertex)
    # g.vs["name"] = range(len(vertex))
    # print(trans)
    R.add_vertices(len(vertex))
    R.vs["name"] = [i for i in range(0, g.vcount())]
    R.add_edges(trans)
    R.es["label"] = trans_labels
    trans_observable_bool = [0 if e in Euo else 1 for e in trans_labels]
    R.es["obs"] = trans_observable_bool
    trans_controllable_bool = [0 if e in Euc else 1 for e in trans_labels]
    R.es["contr"] = trans_controllable_bool
    return R


def add_vertex(vertex, Q, v):
    if v not in vertex:
        vertex.append(v)
        Q.append(v)


def extract_supervisor(arena, X_crit, sup, Euc_new, Euo_new, debug=False):
    # arena: igraph Graph object, made according to construct_arena
    # X_crit: critical states from original plant (NOT states in arena)
    #   e.g. G has X_crit={'bad'}, then arena will have critical states w/ names {('bad','other'), I2, ...}
    # sup: igraph Graph object to store resulting supervisor, assumed to be empty
    # Euc_new, Euo_new: uncontrollable, unobservable events redefined to include compromised events
    last_task, start_time = None, None
    if debug:
        import time

        start_time = time.process_time()
    A = ig.Graph(directed=True)
    A_temp = ig.Graph(directed=True)
    A_obs = ig.Graph(directed=True)

    # preprocessing to meet SPA & subautomata conditions (very slow)
    observer(arena, A_temp, Euo_new, True)
    print(len(A_temp.vs))
    if debug:
        print("First observer computation complete")
        last_task = time.process_time()
        print("Total time: {0}".format(str(last_task - start_time)))

    parallel_comp(A, [arena, A_temp], True)
    # print([(e.source, e["label"],e.target) for e in A.es])
    # print(Euo_new)
    # observer(A, A_temp, Euo_new, True)
    # print(len(A.vs["name"]))
    # print(A_temp.vs["name"])
    if debug:
        print("-----")
        print("Parallel composition complete")
        print("Total time: {0}".format(str(time.process_time() - start_time)))
        print("Segment time: {0}".format(str(time.process_time() - last_task)))
        last_task = time.process_time()

    # A_trim = A.copy()
    A_trim = sup
    A_trim.add_vertices(A.vcount())
    A_trim.add_edges([e.tuple for e in A.es])
    A_trim.es["label"] = A.es["label"].copy()
    A_trim.vs["name"] = A.vs["name"].copy()
    A_trim.vs["adj"] = A.vs["adj"].copy()
    # print([e["label"] for e in A.es])
    # print([type(e) for e in Euc_new ])W
    states_to_remove = {
        v.index
        for v in A_trim.vs
        if X_crit.intersection(
            set(v["name"][v["name"].find("{") + 1 : v["name"].find("}")].split(","))
        )
    }

    split_names = {v["name"]: v["name"].split(" , ") for v in A.vs}
    Atrimnames = A_trim.vs["name"]
    A_trim.vs["name"] = [str(v.index) for v in A_trim.vs]
    A.vs["name"] = [str(v.index) for v in A.vs]
    # print(A.vs["name"])
    scns(A, A_trim, Euc_new, Euo_new, states_to_remove, debug, last_task, start_time)
    if debug:
        print("-----")
        print("SCNS computation complete (incl. 2nd observer computation time)")
        print("Total time: {0}".format(str(time.process_time() - start_time)))
        print("Segment time: {0}".format(str(time.process_time() - last_task)))
        last_task = time.process_time()
    # print(len(A_trim.vs))
    # TODO: sometimes get repeats of states, should be combined
    #   e.g. ex_2_by_2_g.fsm reduced arena will have super w/ 18 states instead of 16 b/c two states each have two vertices w/ same name
    # THEY DO NOT NEED TO BE COMBINE THIS COMES FROM THE SPA AND STATES MUST HAVE DIFERRENT NAMES
    # RENAMING FIXED 04/20 - Romulo

    # print(A_trim.vs["name"])
    names = [Atrimnames[int(i)] for i in A_trim.vs["name"]]
    A_trim.vs["name"] = names

    # print(name_list)
    # print([arena.vs["name"][v["name"][0][0]] for v in A_trim.vs])
    # A_trim.vs["name"] = [(arena.vs["name"][v["name"][0][0]], name_list[i]) for v in A_trim.vs for i in range(len(name_list))]
    # A_trim.vs["name"] = [name_list[i] for i in range(len(name_list))]
    # print(A_trim.vs["name"])
    if debug:
        print("-----")
        print("Final Vcount: {0}".format(A_trim.vcount()))
        print("Total time: {0}".format(str(time.process_time() - start_time)))
        print("-----")


def search(A, X_crit, states_to_keep, Q):
    # Extract a supervisor (not Q1,Q2 states, just an automata)
    # Should be moved to its own function?
    # Not sure how to differentiate this function and the extract_supervisor fn
    # TODO: finish this implementation & test
    while Q:
        c = Q.pop(0)
        states_to_keep.add(c)
        if Q1_state(c, A):
            if c in states_to_keep:
                # If a Q1-like state is found which is also good:
                # can pick the same previously selected state or choose a new one
                cd_set = set(A.es(_source=c))
                # Only add a new control decision (not one that has already been used),
                # as opposed to taking a random control decision or the same cd already taken
                while cd_set:
                    cd = cd_set.pop()
                    if cd.target not in states_to_keep:
                        Q.append(cd.target)
                        break
                    if not cd_set:
                        # If all the possible control decisions have been taken, take the most recent one again
                        # to avoid not selecting a valid control decision (not necessary if just a random cd is taken).
                        Q.append(cd.target)
                # Alternative code to take the cd already taken:
                # Q.append(cd.target)
            else:
                # Select 1 control decision from this Q1 state:
                cd = set(A.es(_source=c)).pop()
            continue
        if Q2_state(c, A):
            Q.extend([e.target for e in A.es(_source=c)])
            continue


def Q1_state(state, graph=None):
    if isinstance(state, int):
        return len(graph.vs[state]["name"]) == 2
    return len(state["name"]) == 2


def Q2_state(state, graph=None):
    if isinstance(state, int):
        return len(graph.vs[state]["name"]) > 2
    return len(state["name"]) > 2
