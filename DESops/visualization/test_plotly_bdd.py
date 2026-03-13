import sys, os

current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.insert(0, current_dir)
sys.path.insert(0, parent_dir)

from bdd_to_plotly import convert_bdd_to_plotly
from plot_bdd_in_plotly import plot_bdd


def read_fsm_to_bdd(fsm_filename):
    """
    Read FSM file and convert to BDD representation WITH TRANSITIONS.
    """
    print(f"📁 Reading FSM file: {fsm_filename}")
    
    if not os.path.exists(fsm_filename):
        raise FileNotFoundError(f"FSM file not found: {fsm_filename}")
    
    state_names = {}
    event_names = {}
    transitions = []  # IMPORTANT: Store actual transitions
    
    with open(fsm_filename, "r") as f:
        # First line: number of states
        line = f.readline().strip()
        n_states = int(line)
        n_states = max(1, n_states - 1)
        
        index = 0
        index_event = 0
        
        for line in f:
            if not line or line == "\n":
                continue
            
            states_tuple = line.split("\t")
            if len(states_tuple) < 3:
                continue
            
            source_name = states_tuple[0]
            if source_name not in state_names:
                binary = bin(index)[2:].zfill(n_states.bit_length())
                state_names[source_name] = binary
                index += 1
            
            num_transitions = int(states_tuple[2])
            
            # Read each transition for this state
            for _ in range(num_transitions):
                trans_line = f.readline()
                if not trans_line:
                    break
                
                trans_tuple = trans_line.split("\t")
                if len(trans_tuple) < 4:
                    continue
                
                event_name = trans_tuple[0]
                target_name = trans_tuple[1]
                
                # Add target state if new
                if target_name not in state_names:
                    binary = bin(index)[2:].zfill(n_states.bit_length())
                    state_names[target_name] = binary
                    index += 1
                
                # Add event if new
                if event_name not in event_names:
                    binary = bin(index_event)[2:].zfill(2)
                    event_names[event_name] = binary
                    index_event += 1
                
                # STORE THE TRANSITION
                transitions.append({
                    'source': source_name,
                    'target': target_name,
                    'event': event_name
                })
        
        # Create dictionaries
        states_dict = {v: k for k, v in state_names.items()}
        events_dict = {v: k for k, v in event_names.items()}
        
        # Create BDD object WITH TRANSITIONS
        bdd_object = {
            'states_dict': states_dict,
            'events_dict': events_dict,
            'transitions': transitions,  # KEY FIX: Include transitions
            'name': os.path.basename(fsm_filename).replace('.fsm', '')
        }
        
        print(f"✅ Created BDD with {len(states_dict)} states, {len(events_dict)} events, {len(transitions)} transitions")
        return bdd_object


# Main execution
print("📖 Reading FSM and converting to BDD...")

# Choose your FSM file
#fsm = os.path.join(parent_dir, "tests", "models", "textbook", "prob_3-28_Kcn.fsm")
#fsm = os.path.join(parent_dir, "tests", "models", "textbook", "prob_3-28_H.fsm")
#fsm = os.path.join(parent_dir, "tests", "models", "textbook", "fig_2-1.fsm")
fsm = os.path.join(os.path.dirname(parent_dir), "tests", "models", "textbook", "fig_2-1.fsm")
#fsm = os.path.join(parent_dir, "tests", "models", "textbook", "fig_3-9_G.fsm")

bdd_object = read_fsm_to_bdd(fsm)

print(f"✅ Loaded: {len(bdd_object['states_dict'])} states, {len(bdd_object['events_dict'])} events, {len(bdd_object['transitions'])} transitions")

# Create BDD visualization
print("🎨 Creating BDD visualization...")
fig = plot_bdd(
    bdd_object,
    title=f"{bdd_object['name']} - BDD Visualization",
    width=1600,
    height=1000,
    show_browser=True,
    save_html=True
)

# Save to file
output_file = os.path.join(current_dir, "bdd_visualization.html")
fig.write_html(output_file)
print(f"✅ Saved to: {output_file}")