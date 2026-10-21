"""
Tests for DESops.verified: the verified validity checker, the trusted wrapper around it
(event table, encode/decode), and Automaton.validate(). Design: DESops-proof/spec/wrapper.md.

The checker itself is proved with Nagini; these tests cover what the proof does not: the trusted
encoding, the result codes as seen from Automaton, and the validated flag.
"""

import random
import subprocess
import sys

import pytest

from DESops.core.automaton import Automaton
from DESops.error import InvalidAutomatonError
from DESops.verified.check import check_automaton
from DESops.verified.encoding import decode, encode, event_table


def chain():
    """x0 -a-> x1 -b-> x2, x0 initial, x2 marked."""
    g = Automaton(events=["a", "b"])
    g.add_state("x0", init=True)
    g.add_state("x1")
    g.add_state("x2", marked=True)
    g.add_transition(0, "a", 1)
    g.add_transition(1, "b", 2)
    return g


def random_automaton(rnd, n, events, density, max_targets=1, n_init=1):
    g = Automaton(events=events)
    for i in range(n):
        g.add_state(f"s{i}", rnd.random() < 0.3, init=i < n_init)
    for i in range(n):
        for e in events:
            if rnd.random() < density:
                for t in rnd.sample(range(n), min(n, rnd.randint(1, max_targets))):
                    g.add_transition(i, e, t)
    return g


def code_of(g, deterministic=False):
    table = event_table([g])
    enc = encode(g, table)
    return check_automaton(enc.n, enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, enc.init,
                           enc.marked, enc.start, enc.evt, enc.dst, deterministic)


def reference_valid(g, deterministic):
    """The spec's conditions (automaton.md section 3), written directly over the class,
    independently of the encoding and the checker."""
    n = len(g.states)
    if (n == 0) != (not g.init):
        return False
    if deterministic and len(g.init) > 1:
        return False
    if not (g.Euc <= g.events and g.Euo <= g.events):
        return False
    for state in g.states:
        for e, targets in state.out.items():
            if e not in g.events:
                return False
            if any(not 0 <= t < n for t in targets):
                return False
            if deterministic and len(targets) > 1:
                return False
    return True


def same_automaton(g, h):
    return (
        [s.name for s in g.states] == [s.name for s in h.states]
        and [s.marked for s in g.states] == [s.marked for s in h.states]
        and g.init == h.init
        and [{e: sorted(t) for e, t in s.out.items()} for s in g.states]
        == [{e: sorted(t) for e, t in s.out.items()} for s in h.states]
        and g.events == h.events and g.Euc == h.Euc and g.Euo == h.Euo
    )


# --- valid automata ------------------------------------------------------------------------


def test_chain_is_valid_dfa():
    g = chain()
    assert code_of(g) == 0 and code_of(g, deterministic=True) == 0
    g.validate(deterministic=True)
    assert g.is_validated


def test_empty_automaton_is_valid():
    g = Automaton()
    assert code_of(g, deterministic=True) == 0
    g.validate(deterministic=True)


def test_encoding_example_from_spec():
    # wrapper.md section 4
    g = Automaton(events=["a", "b"])
    g.add_state("x0", init=True)
    g.add_state("x1")
    g.add_state("x2", marked=True)
    g.add_transition(0, "a", 1)
    g.add_transition(0, "b", 2)
    g.add_transition(1, "a", 0)
    enc = encode(g, {"a": 0, "b": 1})
    assert enc.start == [0, 2, 3, 3]
    assert enc.evt == [0, 1, 0]
    assert enc.dst == [1, 2, 0]
    assert enc.init == [True, False, False]
    assert enc.marked == [False, False, True]


# --- one rejection per condition -----------------------------------------------------------


def test_sizes_code_1():
    assert check_automaton(1, 0, [], [], [], [True], [], [0, 0], [], [], False) == 1


def test_blocks_code_2():
    # start not ending at len(evt)
    assert check_automaton(1, 1, [True], [False], [False], [True], [False],
                           [0, 2], [0], [0], False) == 2


def test_event_not_in_alphabet_code_3():
    g = chain()
    g.events.discard("b")                       # direct edit: W1 now violated
    assert code_of(g) == 3
    with pytest.raises(InvalidAutomatonError, match="W1"):
        g.validate()


def test_target_out_of_range_code_3():
    g = chain()
    g.states[0].out["a"] = [7]                  # direct edit, bypassing add_transition
    assert code_of(g) == 3


def test_euc_not_in_alphabet_code_4():
    g = chain()
    g.Euc.add("z")                              # __init__ adds Euc to events, later edits don't
    assert code_of(g) == 4
    with pytest.raises(InvalidAutomatonError, match="W2"):
        g.validate()


def test_states_without_initial_code_5():
    g = Automaton(events=["a"])
    g.add_state("x0")
    assert code_of(g) == 5
    with pytest.raises(InvalidAutomatonError, match="W3"):
        g.validate()


def test_two_initial_states_code_6():
    g = chain()
    g.init.add(1)
    assert code_of(g) == 0                      # fine as a general automaton
    assert code_of(g, deterministic=True) == 6
    g.validate()
    with pytest.raises(InvalidAutomatonError, match="more than one initial"):
        g.validate(deterministic=True)


def test_nondeterministic_transition_code_7():
    g = chain()
    g.add_transition(0, "a", 2)                 # x0 -a-> {x1, x2}
    assert code_of(g) == 0
    assert code_of(g, deterministic=True) == 7
    with pytest.raises(InvalidAutomatonError, match="same event"):
        g.validate(deterministic=True)


def test_encoder_rejects_non_bool_marking():
    g = chain()
    g.states[1].marked = None
    with pytest.raises(InvalidAutomatonError, match="marked must be bool"):
        g.validate()


def test_encoder_rejects_initial_index_out_of_range():
    g = chain()
    g.init.add(5)
    with pytest.raises(InvalidAutomatonError, match="initial state 5"):
        g.validate()


# --- validated flag ------------------------------------------------------------------------


@pytest.mark.parametrize("mutate", [
    lambda g: g.add_state("x3"),
    lambda g: g.add_states(["x3", "x4"]),
    lambda g: g.add_transition(2, "a", 0),
    lambda g: g.add_transitions([(2, "a", 0)]),
    lambda g: g.remove_transition(0, "a", 1),
    lambda g: g.remove_states([2]),
])
def test_methods_clear_the_flag(mutate):
    g = chain()
    g.validate()
    assert g.is_validated
    mutate(g)
    assert not g.is_validated


def test_flag_levels_and_copy():
    g = chain()
    g.validate()
    assert g._valid == "automaton"
    g.validate(deterministic=True)
    assert g._valid == "dfa"
    g.validate()                                # a DFA is also a valid automaton
    assert g._valid == "dfa"
    assert g.copy()._valid == "dfa"


def test_duplicate_transition_leaves_flag():
    g = chain()
    g.validate()
    with pytest.warns(UserWarning):
        assert g.add_transition(0, "a", 1) is False   # refused, nothing changed
    assert g.is_validated


# --- trusted wrapper: round trips and comparison with the reference ------------------------


def test_round_trip_random():
    rnd = random.Random(0)
    for trial in range(200):
        n = rnd.randint(0, 12)
        g = random_automaton(rnd, n, ["a", "b", "c"], 0.5, max_targets=3,
                             n_init=min(n, rnd.randint(1, 2)))
        g.Euc.add("a")
        g.Euo.add("c")
        table = event_table([g])
        h = decode(encode(g, table), list(table), [s.name for s in g.states])
        assert same_automaton(g, h), trial


def test_checker_matches_reference_on_random_automata():
    rnd = random.Random(1)
    for trial in range(500):
        n = rnd.randint(0, 8)
        g = random_automaton(rnd, n, ["a", "b", "c"], 0.5, max_targets=rnd.choice([1, 2]),
                             n_init=min(n, rnd.randint(0, 2)))
        # random damage, through direct edits the class does not guard against
        r = rnd.random()
        if r < 0.15:
            g.events.discard(rnd.choice(["a", "b", "c"]))
        elif r < 0.3:
            g.Euc.add("z")
        elif r < 0.4 and n:
            g.states[rnd.randrange(n)].out.setdefault("a", []).append(n + 3)
        for det in (False, True):
            assert (code_of(g, det) == 0) == reference_valid(g, det), (trial, det)


def test_runs_without_nagini_installed():
    """The verified modules fall back to no-op contracts when nagini_contracts is missing."""
    code = (
        "import sys; sys.modules['nagini_contracts'] = None; "
        "sys.modules['nagini_contracts.contracts'] = None; "
        "sys.modules['nagini_contracts.obligations'] = None\n"
        "from DESops.core.automaton import Automaton\n"
        "g = Automaton(events=['a']); g.add_state('x', init=True); g.add_transition(0, 'a', 0)\n"
        "g.validate(deterministic=True); print(g.is_validated)\n"
    )
    out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "True"
