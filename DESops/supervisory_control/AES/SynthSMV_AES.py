import itertools
import os
import subprocess
from pathlib import Path

import igraph as ig


def write_AES_SMV_model(G, model_fname):
    create_SMV_file(G, model_fname)

    return


def create_SMV_file(G, model_fname):
    g = G._graph
    ctr = list(G.E - G.Euc)
    print(ctr)
    uctr = list(G.Euc)
    obs = list(G.E - G.Euo)
    # print(obs)
    uobs = list(G.Euo)

    # print(ctr)
    with open(model_fname, "w") as f:
        print("MODULE unobservable_reach(Q,gamma,asg,obs)", file=f)
        print("VAR nX: array 0..{0} of boolean;".format(g.vcount() - 1), file=f)
        print("INIT (!nX[0]", end="", file=f)
        for i in range(g.vcount() - 1):
            print("& !nX[{0}]".format(i + 1), end="", file=f)
        print(")", file=f)
        print("ASSIGN", file=f)
        for v in g.vs:
            print("\tnext(nX[{0}]):=".format(v.index), file=f)
            print("\tcase", file=f)
            action_set = {e["label"] for e in g.es(_target=v.index)}
            print(action_set)
            print("\t\tasg & !obs: Q[{0}];".format(v.index), file=f)
            print("\t\tnX[{0}] & !asg & !obs: TRUE;".format(v.index), file=f)
            for a in action_set:
                if a in G.Euo and a in G.Euc:
                    source_state = [
                        e.source for e in g.es(_target=v.index) if e["label"] == a
                    ]
                    print(source_state)
                    if source_state:
                        print(
                            "\t\t!nX[{0}] & !asg & !obs & (nX[{1}]".format(
                                v.index, source_state[0]
                            ),
                            end="",
                            file=f,
                        )
                        for j in range(len(source_state) - 1):
                            print(" | nX[{0}]".format(source[j + 1]), end="", file=f)
                        print(") & !asg & !obs: TRUE;".format(v.index), file=f)
                elif a in G.Euo and a in ctr:
                    source_state = [
                        e.source for e in g.es(_target=v.index) if e["label"] == a
                    ]
                    print(source_state)
                    if source_state:
                        print(
                            "\t\t!nX[{0}] & !asg & !obs & (nX[{1}]".format(
                                v.index, source_state[0]
                            ),
                            end="",
                            file=f,
                        )
                        for j in range(len(source_state) - 1):
                            print(" | nX[{0}]".format(source[j + 1]), end="", file=f)
                        print(
                            ") & gamma[{0}] & !asg & !obs: TRUE;".format(ctr.index(a)),
                            file=f,
                        )
            print("\t\tobs: nX[{0}];".format(v.index), file=f)
            print("\t\tTRUE: FALSE;", file=f)
            print("\tesac;", file=f)
        # DEFINING THE MAIN MODULE
        print("\nMODULE main", file=f)
        # INPUT VARIABLE
        print("\nIVAR", file=f)
        # OBSERVABLE EVENTS ARE INPUT VARIABLES
        print("\tevents_o: {{{0}, eps}};".format(",".join(obs)), file=f)
        # FOR COMPLETENESS ADD EVENT UOBS, CTR AND UCTR: NOT VARIABLES JUST AS COMMENT
        print("\t--event_uo:", end="", file=f)
        for i in range(len(uobs)):
            print(" {0},".format(uobs[i]), end="", file=f)
        print("", file=f)
        print("\t--event_uc:", end="", file=f)
        for i in range(len(uctr)):
            print(" {0},".format(uctr[i]), end="", file=f)
        print("", file=f)
        print("\t--event_c:", end="", file=f)
        for i in range(len(ctr)):
            print(" {0},".format(ctr[i]), end="", file=f)
        print("", file=f)
        # CONTROL DECISIONS ARE BASED ON EVENTS_C POSITION OF THE EVENT MATCH event_c
        print("\tgammas: array 0..{0} of boolean;".format(len(ctr) - 1), file=f)

        # DEFINING VARIABLES
        print("\nVAR", file=f)
        print("\tQ: array 0..{0} of boolean;".format(g.vcount() - 1), file=f)
        print("\tuoreach: unobservable_reach(Q,gammas,asg,obs);", file=f)
        print("\tobs: boolean;", file=f)
        print("\tasg: boolean;", file=f)
        print("\toldgammas: array 0..{0} of boolean;".format(len(ctr) - 1), file=f)

        # INITIAL STATE OF THE AUTOMATON IS ALWAYS 0
        print("INIT (Q[0]", end="", file=f)
        for i in range(g.vcount() - 1):
            print("& !Q[{0}]".format(i + 1), end="", file=f)
        print(")", file=f)

        # VARIABLE asg
        print("ASSIGN", file=f)
        print("\tinit(asg):=TRUE;", file=f)
        print("\tnext(asg):=", file=f)
        print("\tcase", file=f)
        print("\t\t!obs:FALSE;", file=f)
        print("\t\tobs & events_o!= eps: TRUE;", file=f)
        print("\t\tobs & events_o = eps: FALSE;", file=f)
        print("\tesac;\n", file=f)

        # VARIABLE obs
        print("ASSIGN", file=f)
        print("\tinit(obs):=FALSE;", file=f)
        print("\tnext(obs):=", file=f)
        print("\tcase", file=f)
        print("\t\t!obs", end="", file=f)
        for i in range(g.vcount()):
            print(
                " & uoreach.nX[{0}] = next(uoreach.nX[{0}])".format(i), end="", file=f
            )
        print(": TRUE;", file=f)
        print("\t\tobs & events_o!= eps: FALSE;", file=f)
        print("\t\tobs & events_o = eps: TRUE;", file=f)
        print("\t\tTRUE: FALSE;", file=f)
        print("\tesac;\n", file=f)

        # OBSERVABLE REACH

        print("ASSIGN", file=f)
        for v in g.vs:
            print("\tnext(Q[{0}]):=".format(v.index), file=f)
            print("\tcase", file=f)
            trans_to_v = [e for e in g.es(_target=v.index)]
            action_set = {e["label"] for e in trans_to_v}
            print("\t\t!asg & !obs: uoreach.nX[{0}];".format(v.index), file=f)
            for a in obs:
                if a in action_set:
                    source_state = [e.source for e in trans_to_v if e["label"] == a]
                    # print(source_state)
                    if source_state:
                        print(
                            "\t\t!asg & obs & (Q[{0}]".format(source_state[0]),
                            end="",
                            file=f,
                        )
                        for j in range(len(source_state) - 1):
                            print(
                                " | Q[{0}]".format(source_state[j + 1]), end="", file=f
                            )
                        print(") & events_o = {0}: TRUE;".format(a), file=f)
                        print(
                            "\t\t!asg & obs & !(Q[{0}]".format(source_state[0]),
                            end="",
                            file=f,
                        )
                        for j in range(len(source_state) - 1):
                            print(
                                " | Q[{0}]".format(source_state[j + 1]), end="", file=f
                            )
                        print(") & events_o = {0}: FALSE;".format(a), file=f)
                else:
                    print("\t\t!asg & obs & events_o = {0}: FALSE;".format(a), file=f)
            print("\t\tasg: Q[{0}];".format(v.index), file=f)
            print("\t\tTRUE: Q[{0}];".format(v.index), file=f)
            print("\tesac;", file=f)

        # SAVING PREVIOUS CONTROL DECISION

        print("\nASSIGN", file=f)
        for i in range(len(ctr)):
            print("\tnext(oldgammas[{0}]):= gammas[{0}];".format(i), file=f)

        # RESTRICTION BASED ON ENABLED EVENTS AND ON CURRENT STATE ESTIMATE

        print("\nTRANS", file=f)
        n = len(ctr)
        lst = list(itertools.product([0, 1], repeat=n))
        for v in lst:
            print("\t(", end="", file=f)
            enabled = ["eps"]
            enabled.extend(G.Euc.intersection(set(obs)))
            for i in range(len(v)):
                if v[i] and ctr[i] in obs:
                    enabled.append(ctr[i])
                if i != len(v) - 1:
                    print(
                        "gammas[{0}]={1} & ".format(i, TRUE_FALSE(v[i])), end="", file=f
                    )
                else:
                    print(
                        "gammas[{0}]={1} -> events_o in ".format(i, TRUE_FALSE(v[i])),
                        end="",
                        file=f,
                    )
            print("{{{0}}}) & ".format(",".join(enabled)), file=f)
        print("\t((Q[0]", end="", file=f)
        for i in range(g.vcount() - 1):
            print("| Q[{0}]".format(i + 1), end="", file=f)
        print(") -> (next(Q[0])", end="", file=f)
        for i in range(g.vcount() - 1):
            print("| next(Q[{0}])".format(i + 1), end="", file=f)
        print(")) &", file=f)
        print("\t(", end="", file=f)
        j = 0
        for v in g.vs:
            action_set = [
                e["label"] for e in g.es(_source=v.index) if e["label"] in obs
            ]
            action_set.append("eps")
            # print(action_set)
            print(
                "(Q[{0}] -> events_o in {{{1}}})".format(v.index, ",".join(action_set)),
                end="",
                file=f,
            )
            if j != len(g.vs) - 1:
                print(" | ", end="", file=f)
            else:
                print(") & ", file=f)
            j += 1
        print("\t(!asg -> (", end="", file=f)
        for i in range(len(ctr)):
            if i != len(ctr) - 1:
                print("gammas[{0}] = oldgammas[{0}] & ".format(i), end="", file=f)
            else:
                print("gammas[{0}] = oldgammas[{0}])) ".format(i), file=f)
        print("\nCTRBL obs = FALSE;", file=f)
        print("CTRBL ", end="", file=f)
        for i in range(len(ctr)):
            if i != len(ctr) - 1:
                print(
                    "gammas[{0}] = TRUE |  gammas[{0}] = FALSE | ".format(i),
                    end="",
                    file=f,
                )
            else:
                print("gammas[{0}] = TRUE |  gammas[{0}] = FALSE;".format(i), file=f)
        # print('SYNTH AG !(')
        # for v in G.X_crit:

    return


def TRUE_FALSE(value):
    if not value:
        return "FALSE"
    else:
        return "TRUE"
