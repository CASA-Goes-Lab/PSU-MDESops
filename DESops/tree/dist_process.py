import itertools
from collections import namedtuple

class Pipeline:

    def __init__(self, in_type):
        self.in_type = in_type
        self.out_type = DataType({})
        self.master_type = in_type
        self.process_list = []

    def get_type(self, names):
        return self.master_type.subtype(names)

    def append_process(self, process):
        self.process_list.append(process)
        self.master_type = self.master_type.product_type(process.out_type)
        self.out_type = self.out_type.product_type(process.out_type)

    def check_valid(self):
        if not self.process_list:
            return True
        if not self.in_type.is_subtype(self.process_list[0]):
            return False
        for p1, p2 in zip(self.process_list[:-1], self.process_list[1:]):
            if not p1.out_type.is_subtype(p2.in_type):
                return False
        for i, p1 in enumerate(self.process_list):
            for p2 in self.process_list[i+1:]:
                if not p1.out_type.is_disjoint(p2.out_type):
                    return False
            if not p1.out_type.is_disjoint(self.in_type):
                return False
        return True


class Process:

    def __init__(self, in_type, out_type):
        self.in_type = in_type
        self.out_type = out_type


# TODO: var names are unordered. Need to add check for equality which accounts for this
class DataType:

    def __init__(self, var_value_dict):
        # self._var_value_dict = var_value_dict
        self._var_value_dict = {k: frozenset(v) for k, v in var_value_dict.items()}
        self.TupleClass = namedtuple('datatype', var_value_dict.keys())

    def __call__(self, **kwargs):
        return self.TupleClass(**kwargs)

    def __iter__(self):
        for val in itertools.product(*[self.var_values(name) for name in self.var_names()]):
            yield self.TupleClass._make(val)

    def __eq__(self, other):
        return self._var_value_dict == other._var_value_dict

    def __hash__(self):
        # TODO make sure this is a valid hash
        return hash(frozenset(self._var_value_dict.items()))

    def var_names(self):
        return self._var_value_dict.keys()

    def var_values(self, name):
        return self._var_value_dict[name]

    def subtype(self, names):
        return DataType({name: self._var_value_dict[name] for name in names})

    def is_subtype(self, other):
        for name in self.var_names():
            other_vals = other._var_value_dict.get(name)
            if other_vals is None or not self._var_value_dict[name].issubset(other_vals):
                return False
        return True

    def is_supertype(self, other):
        return other.is_subtype(self)

    def is_disjoint(self, other):
        return self.var_names().isdisjoint(other.var_names())

    def is_type_of(self, val):
        if not val.isinstance(self.TupleClass):
            return False
        for k, v in val._asdict().items():
            if v not in self.var_values(k):
                return False
        return True

    def projection(self, val):
        return self.TupleClass(**{k: v for k, v in val._asdict().items() if k in self.var_names()})

    def inverse_projection(self, val):
        val_dict = val._asdict()
        new_names = list(self.var_names() - val_dict.keys())
        other_values = itertools.product(*[self.var_values(name) for name in new_names])
        return {self.TupleClass(**(val_dict | dict(zip(new_names, o_val)))) for o_val in other_values}

    def inverse_projection_gen(self, val):
        val_dict = val._asdict()
        new_names = list(self.var_names() - val_dict.keys())
        for o_val in itertools.product(*[self.var_values(name) for name in new_names]):
            yield self.TupleClass(**(val_dict | dict(zip(new_names, o_val))))

    '''
    def possible_values(self):
        values = itertools.product(*[self.var_values(name) for name in self.var_names()])
        return {self.TupleClass._make(val) for val in values}
    '''

    def from_subvalues(self, *subvalues):
        return self(**{k: v for sv in subvalues for k, v in sv._asdict().items()})

    def product_type(self, *others):
        var_value_dict = {}
        var_value_dict |= self._var_value_dict
        for other in others:
            var_value_dict |= other._var_value_dict
        return DataType(var_value_dict)

    def quotient_type(self, subtype):
        if not self.is_supertype(subtype):
            raise ValueError("Can only quotient type by a subtype")
        return self.subtype(self.var_names() - subtype.var_names())

    def stringify(self):
        return DataType({str(key): {str(v) for v in vals}
                         for key, vals in self._var_value_dict.items()})

    def is_empty_type(self):
        return len(self.var_names()) == 0

empty_type = DataType({})
empty_value = empty_type()
