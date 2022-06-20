"""
Class representing observation maps of automata systems.
For now only static masks are implemented
"""

from abc import ABC, abstractmethod

from DESops.basic_operations.transducers import transducer_transducer_product, transducer_auto_product, transducer_input_automaton
from DESops.opacity.language_functions import language_inclusion
from DESops.automata import NFA

class ObservationMap(ABC):
    """
    An abstract class representing an observation map that can be applied to an automaton
    This maps the behavior of an automaton as a string to observations of this behavior
    """
    # TODO - make global definition of empty event?
    epsilon = ''

    # abstract methods

    @abstractmethod
    def check_applicable(self, g):
        """
        Check if the observation map is applicable to the given system
        i.e., if the behavior of the automaton is contained in the input behavior of the map

        :param g: The automaton
        :type g: Automata
        :return: Whether or not the map is applicable to the given automaton
        :rtype: bool
        """
        pass

    @abstractmethod
    def apply_observation_map(self, g):
        """
        Construct an automaton encoding observations of the given system

        :param g: The input automaton
        :type g: Automata
        :return: An automaton representing the observed or output behavior through the map
        :rtype: Automata
        """
        pass

    @abstractmethod
    def compose(self, other):
        """
        Construct an observation map resulting from applying this map first, followed by another map

        :param other: The second observation map
        :type other: ObservationMap
        :return: The composed map
        :rtype: ObservationMap
        """
        pass

    @abstractmethod
    def prepend_observation(self, event, obs):
        """
        Modify this observation map to accept its normal input behavior prepended by the given event
        and output prepended by the given observation

        Useful if the observed automaton is modified with a new initial state, for example as in the label transform

        :param event: The prepended event
        :type event: object
        :param obs: The prepended observation
        :type obs: object
        :return: The modified map
        :rtype: ObservationMap
        """
        pass


class StaticMask(ObservationMap):
    """
    Static masks produce observations by mapping a single event to a single observation (both possibly '')
    """

    def __init__(self, *args, **kwargs):
        self._event_map = dict(*args, **kwargs)

    def __getitem__(self, item):
        return self._event_map[item]

    def __setitem__(self, item, data):
        self._event_map[item] = data

    def copy(self):
        new_map = StaticMask(self._event_map)
        return new_map

    def check_applicable(self, g):
        return g.events.issubset(self._event_map.keys())

    def apply_obs_map(self, g):
        g_obs = g.copy()
        g_obs.es['label'] = [self[e] for e in g_obs.es['label']]
        g_obs.events = set(g_obs.es['label'])
        g_obs.Euo = {""}
        g_obs.generate_out()
        return g_obs

    def compose(self, other):
        if isinstance(other, StaticMask):
            return StaticMask({e: other[self[e]] for e in self._event_map.keys()})
        elif isinstance(other, SetValuedStaticMask):
            return SetValuedStaticMask({e: obs for e in self._event_map.keys() for obs in other[e]})
        elif isinstance(other, NonDetDynamicMask):
            '''
            new_trans = other.transducer.copy()
            new_trans.delete_edges(new_trans.es)
            pair_list = [(e.source, e.target) for ev in self._event_map.keys() for e in other.transducer.es if e['label'][0] == self[ev]]
            label_list = [(ev, e['label'][1]) for ev in self._event_map.keys() for e in other.transducer.es if e['label'][0] == self[ev]]
            pair_list += [(e.source, e.target) for e in other.transducer.es if e['label'][0] == self[ev]]
            label_list += [(ev, e['label'][1]) for ev in self._event_map.keys() for e in other.transducer.es if e['label'][0] == self[ev]]
            new_trans.add_edges(pair_list, label_list)
            return NonDetDynamicMask(new_trans)
            '''
            tmp_map = self.to_NonDetDynamicMask()
            return tmp_map.compose(other)
        else:
            raise NotImplementedError('This type of composition is not implemented yet.')

    def prepend_observation(self, event, obs):
        self[event] = obs

    def unobservable_events(self):
        return {e for e in self._event_map.keys() if self[e] == ObservationMap.epsilon}

    def to_NonDetDynamicMask(self):
        transducer = NFA()
        transducer.add_vertex(init=True, marked=True)
        transducer.add_edges([(0, 0)]*len(self._event_map), list(self._event_map.items()))
        transducer.generate_out()
        return NonDetDynamicMask(transducer)


class SetValuedStaticMask(ObservationMap):
    """
    Set valued static masks produce observations by mapping a single event
    to a set of single observations (both possibly '')
    """

    def __init__(self, nd_event_map=None):
        if not nd_event_map:
            nd_event_map = {}
        self._nd_event_map = nd_event_map

    def __getitem__(self, item):
        return frozenset(self._nd_event_map[item])

    def copy(self):
        new_map = SetValuedStaticMask(self._nd_event_map)
        return new_map

    def add_observation(self, event, obs):
        self._nd_event_map.setdefault(event, set()).add(obs)

    def remove_observation(self, event, obs):
        self._nd_event_map[event].remove(obs)

    def check_applicable(self, g):
        return g.events.issubset(self._nd_event_map.keys())

    def apply_obs_map(self, g):
        g_obs = g.copy()
        g_obs.delete_edges(g_obs.es)
        pair_list = [(e.source, e.target) for e in g.es for obs in self[e['label']]]
        label_list = [obs for e in g.es for obs in self[e['label']]]
        g_obs.add_edges(pair_list, label_list)
        g_obs.events = set(g_obs.es['label'])
        g_obs.Euo = {""}
        g_obs.generate_out()
        return g_obs

    def compose(self, other):
        if isinstance(other, StaticMask):
            return SetValuedStaticMask({e: other[inter] for e in self._nd_event_map.keys() for inter in self[e]})
        elif isinstance(other, SetValuedStaticMask):
            return SetValuedStaticMask({e: obs for e in self._nd_event_map.keys() for inter in self[e] for obs in other[inter]})
        elif isinstance(other, NonDetDynamicMask):
            '''
            new_trans = other.transducer.copy()
            new_trans.delete_edges(new_trans.es)
            pair_list = [(e.source, e.target) for ev in self._nd_event_map.keys() for e in other.transducer.es if e['label'][0] in self[ev]]
            label_list = [(ev, e['label'][1]) for ev in self._nd_event_map.keys() for e in other.transducer.es if e['label'][0] in self[ev]]
            new_trans.add_edges(pair_list, label_list)
            return NonDetDynamicMask(new_trans)
            '''
            tmp_map = self.to_NonDetDynamicMask()
            return tmp_map.compose(other)
        else:
            raise NotImplementedError('This type of composition is not implemented yet.')

    def prepend_observation(self, event, obs):
        self.add_observation(event, obs)

    def unobservable_events(self):
        return {e for e in self._nd_event_map.keys() if all([obs == ObservationMap.epsilon for obs in self[e]])}

    def to_NonDetDynamicMask(self):
        transducer = NFA()
        transducer.add_vertex(init=True, marked=True)
        transducer.add_edges([(0, 0)]*len(self._nd_event_map), list(self._nd_event_map.items()))
        transducer.generate_out()
        return NonDetDynamicMask(transducer)


class NonDetDynamicMask(ObservationMap):
    """
    Nondeterministic dynamic masks produce observations by mapping a single event
    to a single observation (both possibly '') evolving itself along a transducer automaton
    """

    def __init__(self, transducer):
        self.transducer = transducer

    def copy(self):
        new_map = NonDetDynamicMask(self.transducer.copy())
        return new_map

    def check_applicable(self, g):
        # TODO : this seems to have weird results with epsilon events
        return language_inclusion(g, transducer_input_automaton(self.transducer), g.events - g.Euo)

    def apply_obs_map(self, g):
        g_attr_list = set()
        if 'secret' in g.vs.attributes():
            g_attr_list.add('secret')
        g_obs = transducer_auto_product(self.transducer, g, g_attr_list=g_attr_list)
        # TODO - use dedicated empty event
        g_obs.Euo = {""}
        return g_obs

    def compose(self, other):
        if isinstance(other, StaticMask):
            # TODO : Make sure this works
            new_trans = self.transducer.copy()
            new_trans.es['label'] = [(e[0], other[e[1]]) for e in new_trans.es['label']]
            return NonDetDynamicMask(new_trans)
        elif isinstance(other, SetValuedStaticMask):
            # TODO: Make sure this works
            new_trans = self.transducer.copy()
            new_trans.delete_edges(new_trans.es)
            pair_list = [(e.source, e.target) for e in self.transducer.es['label'] for obs in other[e[1]]]
            label_list = [(e[0], obs) for e in self.transducer.es['label'] for obs in other[e[1]]]
            new_trans.add_edges(pair_list, label_list)
            return NonDetDynamicMask(new_trans)
        elif isinstance(other, NonDetDynamicMask):
            new_trans = transducer_transducer_product(other.transducer, self.transducer)
            return NonDetDynamicMask(new_trans)
        else:
            raise NotImplementedError('This type of composition is not implemented yet.')

    def prepend_observation(self, event, obs):
        init_states = self.transducer.vs.select(init=True)
        new_init = self.transducer.add_vertex(init=True)
        self.transducer.add_edges([(new_init.index, s.index) for s in init_states], [(event, obs)]*len(init_states))
        init_states['init'] = False


def observable_projection_map(g):
    """
    Create an observation map representing the projection of observable events for the given automaton

    :param g: The automaton
    :type g: Automata
    :return: The map representing projection
    :rtype: StaticMask
    """
    return StaticMask({e: '' if e in g.Euo else e for e in g.events})
