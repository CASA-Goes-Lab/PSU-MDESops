import datetime
import os

import DESops as d
from DESops.opacity.bosy.bosy_interface import run_bosy
from DESops.opacity.bosy.parse_smv import read_smv
from DESops.opacity.bosy.verify import verify_edit_function
from DESops.opacity.contact_tracing.generate_contact_model import contact_example

# choose between running full synthesis, or just parsing existing SMV file
run_synthesis = True
# choose between custom LTL or standard always inference
use_ltl = False
# choose whether we should attempt to simplify transitions using SymPy
simplify = False

if not os.path.exists('contact'):
    os.makedirs('contact')

# model parameters
map_file = "map1.fsm"
num_agents = 2
ids = list(range(num_agents))
pairs = [str(i) + str(j) for i in ids for j in ids if i < j]
base_path = "contact/cntl"

# generate and save model
g, event_var_maps = contact_example(map_file, num_agents)
d.write_fsm("contact/sys.fsm", g)

events = sorted(list(g.events))
inf_vars = [f"c_{p}" for p in pairs]
if use_ltl:
    # generate LTL expression that requires that contact is eventually inferred
    inf_fun = None
    ltl_spec = list()
    for p in pairs:
        inf_var = f"c_{p}"
        contact_events = [e for e in events if p in e]
        ltl_spec.append(f"(!{inf_var} W ({' || '.join(contact_events)}))")
        ltl_spec.append(f"(F({' || '.join(contact_events)}) -> F({inf_var}))")
else:
    # generate functions that return inferences about whether the current event includes a specific contact pair
    ltl_spec = None
    inf_fun = list()
    for p in pairs:
        inf_var = f"c_{p}"
        inf_fun.append(lambda x, e: f"{inf_var}" if p in e else f"!{inf_var}")

# generate valid replacements sets for each event
valid_replaces = dict()
for e_i in events:
    # observer location should match
    valid_replaces[e_i] = {e_o for e_o in events if e_o[1] == e_i[1]}

if run_synthesis:
    os.environ["PATH"] += os.pathsep + "/usr/local/swift/bin/"
    print(f"Synthesis start: {datetime.datetime.now()}\n")
    cntl, preds = run_bosy(
        base_path,
        g,
        ltl_spec=ltl_spec,
        event_var_maps=event_var_maps,
        inf_fun=inf_fun,
        inf_vars=inf_vars,
        ins_bound=1,
        valid_replaces=valid_replaces,
    )
    print(f"Synthesis end: {datetime.datetime.now()}\n")
else:
    cntl, preds = read_smv(
        f"{base_path}.smv",
        g,
        event_var_maps,
        inf_vars,
        allow_insert=False,
        insert_holds_events=True,
    )

success = verify_edit_function(g, cntl)
if success:
    print("Successful obfuscation")
else:
    print("Obfsucation failed")

# save output automata
d.write_fsm(base_path + ".fsm", cntl)

for inf, pred in preds.items():
    pred.vs["marked"] = pred.vs["secret"]
    d.write_fsm(f"contact/pred_{inf}.fsm", pred)
