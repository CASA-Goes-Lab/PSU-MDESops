import igraph as ig

from DESops.basic_operations.observer_comp import observer_comp


def scns(
    A,
    A_trim,
    Euc_new,
    Euo_new,
    states_to_remove,
    debug=False,
    last_task_time=None,
    start_time=None,
):
    not_converged = True
    first_iter = True
    states_removed = set()
    vc, ec = 0, 0
    # print(Euc_new)
    A_obs = ig.Graph(directed=True)
    observer(A, A_obs, Euo_new, True)
    print(len(A_obs.vs))
    # print(A.vs["name"])
    # print(A_obs.vs["name"])
    if debug:
        import time

        print("-----")
        print("Second observer computation complete")
        print("Total time: {0}".format(str(time.process_time() - start_time)))
        print("Segment time: {0}".format(str(time.process_time() - last_task_time)))
        last_task_time = time.process_time()
    while not_converged:
        if not first_iter and not states_to_remove:
            break
        else:
            states_just_removed = scs(A, A_trim, Euc_new, states_to_remove, first_iter)
            if debug:
                print("-----")
                print("SCS iteration")
                print("Total time: {0}".format(str(time.process_time() - start_time)))
                print(
                    "Segment time: {0}".format(
                        str(time.process_time() - last_task_time)
                    )
                )
                last_task_time = time.process_time()
        if not first_iter and not states_just_removed:
            break
        else:
            states_removed.update(states_just_removed)
            states_to_remove = sns(A, A_obs, A_trim, Euc_new, Euo_new, states_removed)
            if debug:
                print("-----")
                print("SNS iteration")
                print("Total time: {0}".format(str(time.process_time() - start_time)))
                print(
                    "Segment time: {0}".format(
                        str(time.process_time() - last_task_time)
                    )
                )
                last_task_time = time.process_time()
        if first_iter:
            first_iter = False
    inacc_states = trim(A_trim)
    A_trim.delete_vertices(inacc_states)


def graphs_equal(G, old_vcount, old_ecount):
    return G.vcount() == old_vcount


def sns(G, G_obs, S, Euc, Euo, states_removed):
    q_dict = dict()
    bad_states = set()
    states_yi = {v["name"] for v in S.vs}
    states_obs = [v[1:-1].split(",") for v in G_obs.vs["name"]]
    # print(states_obs)
    # states_obs = [set(v[1:-1].split(',')) for v in states_obs]
    # print(states_obs)
    Q = list()
    # print([v for v in S.vs])
    for yi in S.vs:
        # print(yi.index)
        for q in states_obs:

            # print(q)
            if yi["name"] in q:
                # Make sure q is in Yi
                if ",".join(q) in q_dict:
                    if not q_dict[",".join(q)]:
                        bad_states.add(yi.index)
                else:
                    # print(set(q[1:-1].split(',')))
                    # print(set(q[1:-1].split(',')).issubset(states_yi))
                    q_dict[",".join(q)] = set(q).issubset(states_yi)
                    if not q_dict[",".join(q)]:
                        # print(yi.index)
                        bad_states.add(yi.index)
    # print(bad_states)
    return bad_states


def scs(G, S, Euc, states_to_remove, first_iter):
    inacc_states = set()
    # states_removed = {S.vs[v]["name"][1] for v in states_to_remove}
    states_removed = set(states_to_remove).difference(inacc_states)
    # S_states_to_remove = {v.index for v in S.vs if v["name"][1] in states_to_remove}
    states_to_check = {
        e.source
        for e in S.es(_target_in=states_to_remove)
        if e["label"] in Euc
        and e.source not in states_removed
        and e.source not in inacc_states
    }

    while states_to_check:
        states_removed.update(states_to_check)
        states_to_check_new = {
            e.source
            for e in S.es(_target_in=states_to_check)
            if e["label"] in Euc
            and e.source not in states_removed
            and e.source not in inacc_states
        }
        states_to_check = states_to_check_new

    G_removed_vs_names = {v for v in states_removed}
    # print(states_removed)
    S.delete_vertices(states_removed)
    if not first_iter:
        inacc_states = trim(S)
    S.delete_vertices(inacc_states)
    return G_removed_vs_names


def trim(G):
    Q = list()
    Q.append(0)
    good_states = set()
    good_states.add(0)
    while Q:
        q = Q.pop(0)
        # neighbors = {t.target for t in G.es(_source_in = q) if t.target not in good_states}
        # print(q)
        # neighbors = {target[0] for target in G.vs["adj"][q]}
        neighbors = {t.target for t in G.es(_source=q) if t.target not in good_states}
        # print(neighbors)
        if not neighbors:
            continue
        in_first = set(Q)
        in_second_but_not_in_first = neighbors - in_first
        good_states = good_states.union(neighbors)
        # print(len(good_states))
        Q.extend(list(in_second_but_not_in_first))
    # print(len(G.vs))
    # print(len(good_states))
    bad_states = {v.index for v in G.vs if v.index not in good_states}
    # print(len(bad_states))
    return bad_states
