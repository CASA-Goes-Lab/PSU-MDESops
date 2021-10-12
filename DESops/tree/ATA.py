"""
Code modeling alternating tree automata.

"""
import boolean
import itertools

from DESops.tree.dist_process import DataType
from DESops.tree.dist_process import empty_type, empty_value
from DESops.automata.NFA import NFA


def _simplify_input(ata_func):
    """
    Decorator simplifying all of the input automata to a function
    """

    def ata_func_wrapper(*args, **kwargs):
        for arg in args:
            if isinstance(arg, ATA):
                arg.simplify()
        for k, arg in kwargs.items():
            if isinstance(arg, ATA):
                arg.simplify()
        return ata_func(*args, **kwargs)

    return ata_func_wrapper


def _simplify_output(ata_func):
    """
    Decorator simplifying the output automata
    """

    def ata_func_wrapper(*args, **kwargs):
        return ata_func(*args, **kwargs).simplify()

    return ata_func_wrapper


def _simplify_io(ata_func):
    """
    Decorator combining the input and output automata
    """
    return _simplify_output(_simplify_input(ata_func))


class ATA:
    """
    Class representing alternating tree automata over infinite words
    This consists of a finite list of states, input types, and direction types.
    The transition function maps states and input labels into a positive boolean
    formula over pairs of states and directions.

    An acceptance condition must also be provided to define the tree language.
    For now we only support Buchi acceptance conditions over "weak" automata.
    This means there is a partition (S_1, S_2, ..., S_n) of the states so that
    i) Each S_i is either accepting or rejecting
    ii) The states of S_i transition only into S_j for j >= i
    A path (q_0 q_1 q_2 ...) is accepted if there exists an accepting S_i so inf(q_0 q_1 ...) is contained in S_i
    """

    def __init__(self, in_type, dir_type):
        # type of labels of trees accepted by this automaton (Sigma)
        self.in_type = in_type
        # type of directions of trees accepted by this automaton (Nu)
        self.dir_type = dir_type
        # states of this automaton (Q)
        self.states = set()
        # initial state of this automaton
        self.init_state = None
        # transitions of this automaton (delta)
        # represented as a dictionary from current state and input label
        # to a monotone boolean formula over the next state and direction
        self.transitions = {}
        # acceptance rabin, streete, parity, Buchi
        self.acceptance_type = None
        # data describing acceptance condition
        self.acceptance = None
        # Construct the algebra over which the transition formulas are defined
        self.alg = boolean.BooleanAlgebra()

    def add_states(self, state_set):
        state_set = set(state_set)
        # add all states from a set to the automaton
        if self.states & state_set:
            raise (ValueError("New states must be disjoint from existing states"))
        self.states |= state_set
        # ensure the transition function is total by adding FALSE transitions
        # this does not change the language accepted by the automaton
        self.transitions |= {(q, sigma): self.alg.FALSE
                             for sigma in self.in_type
                             for q in state_set}

    def add_transitions(self, transitions):
        """
        Add a dict of transitions to the automaton
        these transitions or OR'd with existing transitions so the resulting
        language contains the original language
        """
        for key in transitions.keys():
            self.transitions[key] = self.alg.OR(self.transitions[key], (transitions[key]))

    def set_weak_buchi(self, accepting_set):
        self.acceptance_type = "weak_buchi"
        self.acceptance = accepting_set

    @_simplify_io
    def copy(self, prefix=""):
        """
        Create a copy of the automaton and prefix states with a string
        This requires changing the states to strings
        """
        if self.acceptance_type != "weak_buchi":
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        copy_ata = ATA(self.in_type, self.dir_type)
        copy_ata.states = {prefix + str(q) for q in self.states}
        copy_ata.init_state = prefix + str(self.init_state)
        copy_ata.transitions = {(prefix + str(q), sigma): my_subs(self.transitions[q, sigma], self.alg,
                                                                  lambda key: (prefix + str(key[0]), key[1]))
                                for (q, sigma) in self.transitions.keys()}
        copy_ata.acceptance_type = copy_ata.acceptance_type
        copy_ata.acceptance = {prefix + str(q) for q in self.acceptance}
        return copy_ata

    @_simplify_io
    def copy_int(self, offset=0):
        """
        Create a copy of the automaton and convert states to integers with an offset
        """
        if self.acceptance_type != "weak_buchi":
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        copy_ata = ATA(self.in_type, self.dir_type)
        state_map = {q: i + offset for i, q in enumerate(self.states)}
        copy_ata.states = set(state_map.values())
        copy_ata.init_state = state_map[self.init_state]
        copy_ata.transitions = {(state_map[q], sigma): my_subs(self.transitions[q, sigma], self.alg,
                                                               lambda key: (state_map[key[0]], key[1]))
                                for (q, sigma) in self.transitions.keys()}
        copy_ata.acceptance_type = self.acceptance_type
        copy_ata.acceptance = {state_map[q] for q in self.acceptance}
        return copy_ata

    @_simplify_io
    def AND(self, *others, widen=True):
        """
        Construct the conjunction of this automaton with another
        """
        return self.combine(*others, operation="AND", widen=widen)

    @_simplify_io
    def OR(self, *others, widen=True):
        """
        Construct the disjunction of this automaton with another
        """
        return self.combine(*others, operation="OR", widen=widen)

    @_simplify_io
    def combine(self, *others, operation=None, widen=True):
        """
        Combine this automaton with another.
        Depending on the operation (AND/OR), the resulting language
        will be the intersection or union of the original languages.

        If widen is True, then widen input labels of both to the product of the input labels
        """

        ata_list = [self] + list(others)
        if widen:
            in_type = ata_list[0].in_type.product_type(*[other.in_type for other in ata_list[1:]])
            ata_list = [ata.widen_output(in_type) for ata in ata_list]

        if len({ata.acceptance_type for ata in ata_list}) != 1:
            raise ValueError("Mismatch in ATA acceptance types")
        if len({ata.in_type for ata in ata_list}) != 1:
            raise ValueError("Mismatch in ATA input labels")
        if len({ata.dir_type for ata in ata_list}) != 1:
            raise ValueError("Mismatch in ATA direction labels")
        if operation not in {"AND", "OR"}:
            raise ValueError("Combine operation must be 'AND' or 'OR'")

        # Create a union automaton with states and transitions copied from both automata
        union_ata = ATA(ata_list[0].in_type, ata_list[0].dir_type)

        offset = 0
        copy_list = []
        for ata in ata_list:
            copy_ata = ata.copy_int(offset)
            copy_list.append(copy_ata)
            offset += len(ata.states)
            union_ata.add_states(copy_ata.states)
            union_ata.add_transitions(copy_ata.transitions)

        # Introduce new init state with outgoing transitions mirroring the init states from both automata
        union_init = offset
        union_ata.add_states({union_init})
        union_ata.init_state = union_init
        for sigma in copy_list[0].in_type:
            t_list = [copy_ata.transitions[copy_ata.init_state, sigma] for copy_ata in copy_list]
            t = _AND_list(union_ata.alg, t_list) if operation == "AND" else _OR_list(union_ata.alg, t_list)
            union_ata.add_transitions({(union_init, sigma): t})

        if copy_list[0].acceptance_type == "weak_buchi":
            union_ata.set_weak_buchi(set().union(*[ata.acceptance for ata in copy_list]))
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        return union_ata

    @_simplify_io
    def complement(self):
        """
        Alter the automaton to accept the complement of the language it accepts
        """
        self.transitions = {k: dualize(v)
                            for k, v in self.transitions.items()}
        if self.acceptance_type == "weak_buchi":
            self.set_weak_buchi(self.states - self.acceptance)
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        return self

    def simplify(self):
        """
        Simplify all boolean expressions in the transition of the automaton
        by putting them in disjunctive normal form
        """
        self.transitions = {key: _dnf(self.alg, val) for key, val in self.transitions.items()}
        return self

    @_simplify_io
    def accessible_part(self):
        reached_states = set()
        new_states = {self.init_state}
        while new_states := new_states - reached_states:
            state = new_states.pop()
            reached_states.add(state)
            new_states.update({v[0] for sigma in self.in_type
                               for v in self.transitions[state, sigma].args
                               })
        acc_ata = ATA(self.in_type, self.dir_type)
        acc_ata.add_states(reached_states)
        acc_ata.init_state = self.init_state
        acc_ata.add_transitions({(q, sigma): self.transitions[q, sigma]
                                 for q in reached_states for sigma in self.in_type})

        if self.acceptance_type == "weak_buchi":
            acc_ata.set_weak_buchi(self.acceptance & reached_states)
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return acc_ata

    @_simplify_io
    def to_nondet(self):
        """
        Construct a non-deterministic (non-alternating) automaton accepting the same languages
        """
        nta = ATA(self.in_type, self.dir_type)
        nta.init_state = frozenset([self.init_state])
        new_states = {nta.init_state}
        while new_states := (new_states - nta.states):
            q_set = new_states.pop()
            # print(len(new_states))
            # print(q_set)
            nta.add_states({q_set})
            for sigma in self.in_type:
                q_list = []
                for q in q_set:
                    if self.transitions[q, sigma] == False:
                        nta.transitions[q_set, sigma] = nta.alg.FALSE
                        q_list = None
                        break
                    if self.transitions[q, sigma] != True:
                        q_list.append(q)
                if q_list is None:
                    continue
                if not q_list:
                    nta.transitions[q_set, sigma] = nta.alg.TRUE
                    continue

                orig_trans = _dnf(nta.alg, _AND_list(nta.alg, [
                    self.transitions[q, sigma] for q in q_list
                ]))
                new_or_terms = []
                for or_term in _or_terms(orig_trans):
                    dir_map = {}
                    for (q, nu) in or_term.objects:
                        if nu not in dir_map:
                            dir_map[nu] = set()
                        dir_map[nu].add(q)
                    dir_map = {k: frozenset(v) for k, v in dir_map.items()}
                    new_or_terms.append(_AND_list(nta.alg, [
                        nta.alg.Symbol((v, k)) for k, v in dir_map.items()
                    ]))
                    new_states.update(dir_map.values())
                nta.transitions[q_set, sigma] = _OR_list(nta.alg, new_or_terms)

        if self.acceptance_type == "weak_buchi":
            nta.set_weak_buchi({s for s in nta.states if all(q in self.acceptance for q in s)})
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return nta

    @_simplify_input
    def is_nondet(self):
        """
        Check if the automaton is non-deterministic
        """
        for trans_form in self.transitions.values():
            if trans_form == True or trans_form == False:
                continue
            for term in _or_terms(trans_form):
                directions = [obj[1] for obj in term.objects]
                if len(directions) != len(set(directions)):
                    return False
        return True

    @_simplify_input
    def is_universal(self):
        """
        Check if the automaton is universal
        """
        result = self.complement().is_nondet()
        self.complement()
        return result

    @_simplify_input
    def is_det(self):
        """
        Check if the automaton is deterministic (both universal and non-deterministic)
        """
        return self.is_nondet() and self.is_universal()

    @_simplify_input
    def is_tree(self):
        if not self.is_det():
            return False
        return all(len([sigma for sigma in self.in_type if self.transitions[q, sigma] != False]) for q in self.states)

    @_simplify_input
    def accepts_tree(self, tree_dta):
        """
        Check if the automaton accepts this tree represented as a deterministic tree automaton
        """
        if not tree_dta.is_tree():
            raise ValueError("Tree must be represented by deterministic tree automaton")
        empty, _ = self.AND(tree_dta).to_nondet().is_empty()
        return not empty

    @_simplify_input
    def is_empty(self):
        """
        Check if the language accepted by the automaton is empty.
        Automaton must be non-deterministic
        """
        if self.acceptance_type != 'weak_buchi':
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        if not self.is_nondet():
            raise ValueError("Automaton is not nondeterministic")
        ata = self.copy_int()

        good_accepting_states = ata.acceptance.copy()
        good_accepting_trans = ata.transitions.copy()
        # Find accepting cycles
        while True:
            # print("GOOD: ", good_accepting_states)
            # set transitions outside of good_accepting_states to False
            good_accepting_trans = {key: my_subs(val, ata.alg,
                                                 lambda v: v if v[0] in good_accepting_states else None,
                                                 none_value=False).simplify()
                                    for key, val in good_accepting_trans.items()}
            # Bad states have no transition to a good state
            new_bad_states = {q for q in good_accepting_states if all(
                good_accepting_trans[q, d] == False
                for d in ata.in_type
            )}
            # If no new bad states were found, then we have found all accepting cycles
            if not new_bad_states:
                break
            # Otherwise remove the bad states and continue iterating
            good_accepting_states -= new_bad_states

        good_seq = [good_accepting_states, good_accepting_states]
        is_empty = None
        # Determine if initial state can reach accepting cycles
        while True:
            good_states = good_seq[-1].copy()
            # If initial state can reach accepting cycle, then language is non-empty
            if ata.init_state in good_states:
                is_empty = False
                break
            # Otherwise set transitions to good states to True
            ata.transitions = {key: _dnf(ata.alg, my_subs(val, ata.alg,
                                                          lambda v: None if v[0] in good_states else v,
                                                          none_value=True))
                               for key, val in ata.transitions.items()}

            # New good states are those which have some True transition
            new_good_states = {q for q in ata.states - good_states if any(
                ata.transitions[q, d] == True
                for d in ata.in_type
            )}
            # if no new good states were found, then language is empty
            if not new_good_states:
                is_empty = True
                break
            # otherwise add new good states
            good_states |= new_good_states
            good_seq.append(good_states)
        if is_empty:
            return True, None

        # TODO - this is broken
        """
        dta = ATA(ata.in_type, ata.dir_type)
        dta.add_states(ata.states)
        dta.init_state = ata.init_state
        dta.set_weak_buchi(ata.acceptance)
        for source_set, target_set in zip(good_seq[1:], good_seq[:-1]):
            if not source_set.issubset(target_set):
                source_set -= target_set
            for q in source_set:
                for sigma in dta.in_type:
                    if ata.transitions[q, sigma] == True:
                        x = my_subs(self.transitions[q, sigma], dta.alg,
                                    lambda v: v if v[0] in target_set else None,
                                    none_value=False)
                        dta.transitions[q, sigma] = _or_terms(
                            _dnf(dta.alg, my_subs(self.transitions[q, sigma], dta.alg,
                                                  lambda v: v if v[0] in target_set else None,
                                                  none_value=False)))[0]  # pick any term (first for simplicity)
                        break
        dta = dta.accessible_part()
        return False, dta
        """
        return False, None

    @_simplify_io
    def widen_output(self, in_supertype):
        """
        Convert an automaton accepting  Sigma-labeled Nu-trees to
        an automaton accepting XiSigma-labeled Nu-trees (where XiSigma is
        a supertype of Sigma) that accepts exactly
        the trees that are widenings (via type inverse projection) of trees accepted
        by the original
        """
        if not self.in_type.is_subtype(in_supertype):
            raise ValueError("Type must be supertype of automaton's input type")

        n_ata = ATA(in_supertype, self.dir_type)
        n_ata.states = self.states.copy()
        n_ata.init_state = self.init_state
        n_ata.transitions = {(q, in_val_mod): val
                             for (q, in_val), val in self.transitions.items()
                             for in_val_mod in in_supertype.inverse_projection_gen(in_val)}

        n_ata.acceptance_type = self.acceptance_type
        n_ata.acceptance = self.acceptance

        return n_ata

    @_simplify_io
    def narrow(self, dir_subtype):
        """
        Convert an automaton accepting  Sigma-labeled XiNu-trees to
        an automaton accepting Sigma-labeled Xi-trees (where Xi is a subtype of XiNu)
        whose Nu-widenings are accepted by the original
        """
        assert dir_subtype.is_subtype(self.dir_type)
        # if self.acceptance_type != 'weak_buchi':
        #    raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        n_ata = ATA(self.in_type, dir_subtype)
        n_ata.states = self.states.copy()
        n_ata.init_state = self.init_state
        n_ata.transitions = {key: my_subs(val, self.alg, lambda v: (v[0], dir_subtype.projection(v[1])))
                             for key, val in self.transitions.items()}
        n_ata.acceptance_type = self.acceptance_type
        n_ata.acceptance = self.acceptance

        return n_ata

    @_simplify_io
    def cover(self):
        """
        Convert automaton accepting NuSigma-labeled Nu-trees to
        an automaton accepting Sigma-labeled Nu-trees (where NuSigma
        is the product type of Nu and Sigma) whose xrays are
        accepted by the original
        """
        assert self.dir_type.is_subtype(self.in_type)
        in_subtype = self.in_type.subtype(self.in_type.var_names() - self.dir_type.var_names())
        cov_ata = ATA(in_subtype, self.dir_type)
        cov_ata.states = {(q, nu) for q in self.states for nu in self.dir_type}
        cov_ata.init_state = (self.init_state, next(iter(self.dir_type)))
        cov_ata.transitions = {((q, nu), sigma): my_subs(
            self.transitions[q, self.in_type.from_subvalues(sigma, nu)], self.alg,
            lambda v: ((v[0], v[1]), v[1]))
            for q in self.states for nu in self.dir_type
            for sigma in in_subtype}

        if self.acceptance_type == 'weak_buchi':
            cov_ata.set_weak_buchi({(q, nu) for q in self.acceptance for nu in self.dir_type})
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return cov_ata

    @_simplify_io
    def delay_input(self):
        cov_ata = ATA(self.in_type, self.dir_type)
        cov_ata.states = {(q, nu) for q in self.states for nu in self.dir_type}
        cov_ata.init_state = (self.init_state, next(iter(self.dir_type)))
        cov_ata.transitions = {((q, nu), sigma): _AND_list(self.alg, [my_subs(
            self.transitions[q, sigma], self.alg,
            lambda v: ((v[0], nu_n), nu_n) if v[1] == nu else None,
            none_value=True) for nu_n in self.dir_type])
                               for q in self.states for nu in self.dir_type
                               for sigma in self.in_type}

        if self.acceptance_type == 'weak_buchi':
            cov_ata.set_weak_buchi({(q, nu) for q in self.acceptance for nu in self.dir_type})
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return cov_ata

    @_simplify_io
    def delay_input_mod(self):
        cov_ata = ATA(self.in_type, self.dir_type)
        cov_ata.init_state = _get_unique_name(self.states, "d_")
        cov_ata.add_states({(q, nu) for q in self.states for nu in self.dir_type})
        cov_ata.add_states({cov_ata.init_state})
        cov_ata.transitions |= {((q, nu), sigma): _AND_list(self.alg, [my_subs(
            self.transitions[q, sigma], self.alg,
            lambda v: ((v[0], nu_n), nu_n) if v[1] == nu else None,
            none_value=True) for nu_n in self.dir_type])
                                for q in self.states for nu in self.dir_type
                                for sigma in self.in_type}
        cov_ata.add_transitions({(cov_ata.init_state, sigma):
                                     _AND_list(self.alg, [self.alg.Symbol(((self.init_state, nu), nu))
                                                          for nu in self.dir_type])
                                 for sigma in self.in_type})

        if self.acceptance_type == 'weak_buchi':
            cov_ata.set_weak_buchi({(q, nu) for q in self.acceptance for nu in self.dir_type})
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return cov_ata

    @_simplify_io
    def delay_in(self, in_subtype):
        quotient_in_type = self.in_type.quotient_type(in_subtype)
        cov_ata = ATA(self.in_type, self.dir_type)
        cov_ata.init_state = _get_unique_name(self.states, "d_")
        cov_ata.add_states({(q, xi) for q in self.states for xi in quotient_in_type})
        cov_ata.add_states({cov_ata.init_state})
        cov_ata.transitions |= {((q, xi), self.in_type.from_subvalues(xip, sigma)): my_subs(
            self.transitions[q, self.in_type.from_subvalues(xi, sigma)], self.alg,
            lambda v: ((v[0], xip), v[1]))
            for q in self.states for xi in quotient_in_type
            for xip in quotient_in_type for sigma in in_subtype}
        sigma_0 = next(iter(in_subtype))

        cov_ata.add_transitions({(cov_ata.init_state, self.in_type.from_subvalues(xi, sigma_0)):
                _AND_list(self.alg, [self.alg.Symbol(((self.init_state, xi), nu)) for nu in self.dir_type])
             for xi in quotient_in_type})
        if self.acceptance_type == 'weak_buchi':
            cov_ata.set_weak_buchi({(q, xi) for q in self.acceptance for xi in quotient_in_type})
        else:
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")
        return cov_ata

    @_simplify_io
    def change_pipeline(self, in_to_dir_type, mode='OR', delay=False):
        """
        For pipeline architectures
        Convert a non-deterministic automaton accepting XiSigma-labeled Theta trees
        to one that accepts Sigma-labeled Xi trees that can be composed
        with a Xi-labeled Theta tree (where XiSimga is the product type of Xi and Sigma)
        is a subtype of XiSigma) to yield a tree accepted by the original
        """
        if mode == 'AND':
            if not delay:
                remaining_in_type = self.in_type.quotient_type(in_to_dir_type)
                ata = self.delay_in(remaining_in_type).complement()
            else:
                ata = self.complement()
            ata = ata.change_pipeline(in_to_dir_type, mode="OR", delay=True).complement()
            if delay:
                self.complement()
            return ata
        if mode != 'OR':
            raise ValueError("Mode must be AND or OR")

        if not in_to_dir_type.is_subtype(self.in_type):
            raise ValueError("Provided type must be subtype of input type")

        ata = self if self.is_nondet() else self.to_nondet()

        #remaining_in_type = ata.in_type.subtype(ata.in_type.var_names() - in_to_dir_type.var_names())
        remaining_in_type = ata.in_type.quotient_type(in_to_dir_type)
        # TODO make it more clear which way we delay, maybe use more descriptive name
        if not delay:
            ata = ata.delay_in(remaining_in_type)

        c_ata = ATA(remaining_in_type, in_to_dir_type)
        c_ata.add_states(ata.states)
        c_ata.init_state = ata.init_state

        for q in ata.states:
            for sigma in remaining_in_type:
                or_terms = []
                for xi in in_to_dir_type:
                    f = _or_terms(ata.transitions[q, ata.in_type.from_subvalues(xi, sigma)])
                    if f is None:
                        or_terms = None
                        break
                    for term in f:
                        or_terms.append(_AND_list(ata.alg,
                                                  [ata.alg.Symbol((fq, xi)) for (fq, theta) in term.objects]))
                c_ata.transitions[q, sigma] = _OR_list(ata.alg, or_terms)

        c_ata.acceptance_type = ata.acceptance_type
        c_ata.acceptance = ata.acceptance

        return c_ata

    @_simplify_input
    def is_word_automata(self):
        """
        Check if this automaton has only trivial direction type
        """
        return self.dir_type.is_empty_type()

    @_simplify_io
    def to_tree_automaton(self, dir_type):
        """
        Convert a word automaton accepting paths to a tree automaton
        accepting trees over the provided direction where every branch
        of the tree augmented with the direction is a path accepted
        by the original automaton

        This converts a linear specification over inputs and outputs
        to a specification over output-labeled input-trees.
        """
        if not self.is_word_automata():
            raise ValueError("Must be word automaton")
        return self.change_pipeline(dir_type, mode='AND')

    @_simplify_input
    def to_buchi_NFA(self):
        """
        Construct an NFA where marked states represent a Buchi acceptance condition that
        accepts the same words as this automaton.
        Can only perform this construction for non-deterministic word automata
        """
        if not self.is_word_automata():
            raise ValueError("Converting to NFA is only possible for trivial direction type.")

        if self.acceptance_type != 'weak_buchi':
            raise NotImplementedError("Only 'weak_buchi' acceptance conditions are supported for now")

        if not self.is_nondet():
            raise ValueError("Automaton must be nondeterministic")
        nta = self

        state_map = {q: i for i, q in enumerate(nta.states)}

        g = NFA()
        g.add_vertices(len(nta.states), names=[str(q) for q in nta.states])
        g.vs['init'] = False
        g.vs[state_map[nta.init_state]]['init'] = True
        g.vs['marked'] = False
        for q in nta.acceptance:
            g.vs['marked'][state_map[q]] = True

        need_live_state = any(t == True for t in nta.transitions.values())
        if need_live_state:
            live_state = len(nta.states)
            g.add_vertices(1, names=['live'])
            g.add_edges(*zip(*[((live_state, live_state), sigma) for sigma in nta.in_type]))
            g.vs[live_state]['marked'] = True
            g.vs[live_state]['init'] = False

        for q in nta.states:
            for sigma in nta.in_type:
                suc_terms = _or_terms(nta.transitions[q, sigma])
                if suc_terms is None:
                    g.add_edge(state_map[q], live_state, sigma)
                    continue
                if suc_terms:
                    g.add_edges(*zip(*[((state_map[q], state_map[term.obj[0]]), sigma) for term in suc_terms]))

        return g


class AWA(ATA):
    """
    Class representing alternating word automata
    Convenience for now, might remove later.
    """

    def __init__(self, in_type):
        dir_type = DataType({})
        super().__init__(in_type, dir_type)

    @staticmethod
    def from_Buchi_NFA(g):
        g_awa = AWA()
        pass


def dualize(expr):
    """
    Dualize the expression by swapping AND and OR
    """
    c_expr = expr.simplify()
    return _dualize(c_expr)


def _dualize(expr):
    # helper func for dualize
    if expr.isliteral:
        return expr
    if expr == True:
        return expr.FALSE
    if expr == False:
        return expr.TRUE
    return expr.dual(*(_dualize(ar) for ar in expr.args))


def _dnf(alg, expr):
    """
    More consistent version for computing disjunctive normal form
    Default version has bug with dualizing True and False:
        alg.dnf(alg.FALSE).FALSE is None but should be alg.FALSE instead.
    """
    expr = expr.simplify()
    if expr == False:
        return expr
    if expr == True:
        return expr
    return alg.dnf(expr).simplify()


def my_subs(expr, alg, sub_func, none_value=None):
    """
    Perform a substitution on a boolean expression according to a function on its objects
    """
    # convert a function over objects to a substitution dictionary over symbols and apply it to an expression
    if none_value == False:
        def sym_func(k):
            tmp = sub_func(k.obj)
            return alg.FALSE if tmp is None else alg.Symbol(tmp)
    elif none_value == True:
        def sym_func(k):
            tmp = sub_func(k.obj)
            return alg.TRUE if tmp is None else alg.Symbol(tmp)
    else:
        def sym_func(k):
            return alg.Symbol(sub_func(k.obj))
    return expr.subs({sym: sym_func(sym) for sym in expr.symbols})


def _or_terms(form):
    """
    Get the or terms from a boolean formula (expected to be in disjunctive normal form)
    """
    if form == False:
        return []
    if form == True:
        return None
    if form.isliteral or form.operator == '&':
        return [form]
    return list(form.args)


def _AND_list(alg, formulas):
    """
    Compute the conjunction (AND) of a list of formulas
    Handles edge cases as expected
    """
    if formulas is None:
        return alg.FALSE
    if not formulas:
        return alg.TRUE
    if len(formulas) == 1:
        return formulas[0]
    return alg.AND(*formulas)


def _OR_list(alg, formulas):
    """
    Compute the disjunction (OR) of a list of formulas
    Handles edge cases as expected
    """
    if formulas is None:
        return alg.TRUE
    if not formulas:
        return alg.FALSE
    if len(formulas) == 1:
        return formulas[0]
    return alg.OR(*formulas)


def _get_unique_name(existing_names, base_name=""):
    if isinstance(base_name, int):
        name_func = lambda x: base_name + x
    else:
        base_name = str(base_name)
        name_func = lambda x: base_name + str(x)
    return next(name_func(x) for x in range(len(existing_names) + 1) if name_func(x) not in existing_names)
