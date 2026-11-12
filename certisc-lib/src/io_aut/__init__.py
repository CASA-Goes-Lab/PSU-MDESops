"""
Reading and writing automata (part of the certisc distribution). Public API:

- read_aut(path) -> ValidAutomaton      certisc's JSON format (aut_json.py)
- write_aut(G, path)                    writes it (G: ValidAutomaton or Automaton)
- from_dict(d) -> Automaton, to_dict(G) the same, without files
- read_fsm(path) -> ValidAutomaton      imports DESUMA .fsm models (fsm.py)
- read_cif(path) -> EfsmSystem          reads CIF 3 models (Eclipse ESCET) as EFSMs (cif.py);
  parse_cif(text) -> EfsmSystem         the same, from a string. Unsupported CIF constructs
                                        raise UnsupportedCifError, never get skipped.

The readers are trusted code that only build the automaton; validity is decided by the
verified checker (core_aut.validate), so a reader bug becomes an error, never an invalid
automaton.
"""

from io_aut.aut_json import from_dict, read_aut, to_dict, write_aut
from io_aut.cif import CifFormatError, UnsupportedCifError, parse_cif, read_cif
from io_aut.fsm import read_fsm

__all__ = ["read_aut", "write_aut", "from_dict", "to_dict", "read_fsm", "read_cif", "parse_cif",
           "CifFormatError", "UnsupportedCifError"]
