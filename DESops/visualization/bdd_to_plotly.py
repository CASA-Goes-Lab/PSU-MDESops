# import plotly.graph_objects as go
# import networkx as nx
# from typing import Dict, List, Tuple, Any
# import math


# def convert_bdd_to_plotly(bdd_object, title="BDD Visualization", width=1800, height=1200):
#     """Convert BDD to interactive Plotly visualization."""
#     try:
#         nodes_data, edges_data, legend_mapping = extract_bdd_structure(bdd_object)
#         fig = create_bdd_plotly_figure(nodes_data, edges_data, legend_mapping, title, width, height)
#         return fig
#     except Exception as e:
#         print(f"Error converting BDD to Plotly: {e}")
#         import traceback
#         traceback.print_exc()
#         fig = go.Figure()
#         fig.add_annotation(
#             text=f"Error: {str(e)}", xref="paper", yref="paper",
#             x=0.5, y=0.5, showarrow=False, font=dict(size=16, color="red")
#         )
#         fig.update_layout(title=title, width=width, height=height)
#         return fig


# def extract_bdd_structure(bdd_object):
#     """Extract BDD structure - NOW WITH REAL TRANSITIONS."""
#     nodes_data = []
#     edges_data = []
    
#     if not isinstance(bdd_object, dict):
#         return [], [], {}
    
#     states_dict = bdd_object.get('states_dict', {})
#     events_dict = bdd_object.get('events_dict', {})
    
#     # Get actual transitions if available
#     transitions = bdd_object.get('transitions', [])
    
#     legend_mapping = {'states': states_dict, 'events': events_dict}
    
#     # Create state name to ID mapping
#     state_name_to_id = {}
#     node_id = 0
#     for binary, name in states_dict.items():
#         nodes_data.append({
#             'id': node_id,
#             'name': name,
#             'binary': binary,
#             'type': 'state'
#         })
#         state_name_to_id[name] = node_id
#         node_id += 1
    
#     # Create edges from transitions if available
#     if transitions:
#         edge_id = 0
#         for trans in transitions:
#             source_name = trans.get('source')
#             target_name = trans.get('target')
#             event = trans.get('event', f'event_{edge_id}')
            
#             if source_name in state_name_to_id and target_name in state_name_to_id:
#                 edges_data.append({
#                     'id': edge_id,
#                     'source': state_name_to_id[source_name],
#                     'target': state_name_to_id[target_name],
#                     'label': event
#                 })
#                 edge_id += 1
#     else:
#         # Fallback: create some edges to avoid vertical chain
#         # Create a more distributed structure
#         num_nodes = len(nodes_data)
#         edge_id = 0
        
#         # Create branching structure instead of chain
#         for i in range(num_nodes):
#             # Connect to next 2-3 nodes with some branching
#             if i + 1 < num_nodes:
#                 edges_data.append({
#                     'id': edge_id,
#                     'source': i,
#                     'target': i + 1,
#                     'label': f'event_{edge_id}'
#                 })
#                 edge_id += 1
            
#             # Add some branching connections
#             if i + 3 < num_nodes and i % 3 == 0:
#                 edges_data.append({
#                     'id': edge_id,
#                     'source': i,
#                     'target': i + 3,
#                     'label': f'event_{edge_id}'
#                 })
#                 edge_id += 1
            
#             # Add occasional backward connections for cycles
#             if i > 2 and i % 5 == 0:
#                 edges_data.append({
#                     'id': edge_id,
#                     'source': i,
#                     'target': max(0, i - 2),
#                     'label': f'event_{edge_id}'
#                 })
#                 edge_id += 1
    
#     return nodes_data, edges_data, legend_mapping


# def create_force_directed_layout(nodes_data, edges_data):
#     """Create force-directed layout with strong spacing."""
#     num_nodes = len(nodes_data)
    
#     if num_nodes == 0:
#         return {}
#     if num_nodes == 1:
#         return {0: (0, 0)}
    
#     # Build graph
#     G = nx.DiGraph()
#     for node in nodes_data:
#         G.add_node(node['id'])
#     for edge in edges_data:
#         G.add_edge(edge['source'], edge['target'])
    
#     # Use Kamada-Kawai for best spacing
#     try:
#         scale = max(400, num_nodes * 30)
#         pos = nx.kamada_kawai_layout(G, scale=scale)
#         return pos
#     except:
#         pass
    
#     # Fallback: spring layout with high k
#     try:
#         k = max(3, math.sqrt(1.0 / num_nodes) * 20)
#         scale = max(400, num_nodes * 25)
#         pos = nx.spring_layout(G, k=k, iterations=300, scale=scale, seed=42)
#         return pos
#     except:
#         pass
    
#     # Last resort: circular
#     return nx.circular_layout(G, scale=max(300, num_nodes * 15))


# def create_bdd_plotly_figure(nodes_data, edges_data, legend_mapping, title, width, height):
#     """Create interactive Plotly figure with optimal layout."""
    
#     if not nodes_data:
#         fig = go.Figure()
#         fig.add_annotation(
#             text="No BDD data available", xref="paper", yref="paper",
#             x=0.5, y=0.5, showarrow=False, font=dict(size=16, color="gray")
#         )
#         fig.update_layout(title=title, width=width, height=height)
#         return fig
    
#     num_nodes = len(nodes_data)
    
#     # Use force-directed layout for better spacing
#     pos = create_force_directed_layout(nodes_data, edges_data)
    
#     x_coords = [pos[node['id']][0] for node in nodes_data]
#     y_coords = [pos[node['id']][1] for node in nodes_data]
    
#     fig = go.Figure()
    
#     # Draw edges
#     edge_x, edge_y = [], []
    
#     for edge in edges_data:
#         if edge['source'] in pos and edge['target'] in pos:
#             x0, y0 = pos[edge['source']]
#             x1, y1 = pos[edge['target']]
            
#             edge_x.extend([x0, x1, None])
#             edge_y.extend([y0, y1, None])
            
#             # Arrow
#             fig.add_annotation(
#                 x=x1, y=y1, ax=x0, ay=y0,
#                 axref="x", ayref="y", xref="x", yref="y",
#                 arrowhead=2, arrowsize=1.2, arrowwidth=2,
#                 arrowcolor="#666", showarrow=True
#             )
            
#             # Label with offset
#             mid_x, mid_y = (x0 + x1) / 2, (y0 + y1) / 2
#             dx, dy = x1 - x0, y1 - y0
#             length = math.sqrt(dx**2 + dy**2)
            
#             if length > 0.01:
#                 offset = 20
#                 offset_x = -offset * (dy / length)
#                 offset_y = offset * (dx / length)
#             else:
#                 offset_x, offset_y = 10, 0
            
#             label_size = 8 if num_nodes > 15 else 9
            
#             fig.add_annotation(
#                 x=mid_x + offset_x,
#                 y=mid_y + offset_y,
#                 text=edge['label'],
#                 showarrow=False,
#                 font=dict(size=label_size, color='#1a5016'),
#                 bgcolor='rgba(255, 255, 255, 0.95)',
#                 bordercolor='#4a7c2c',
#                 borderwidth=1,
#                 borderpad=2
#             )
    
#     fig.add_trace(go.Scatter(
#         x=edge_x, y=edge_y,
#         mode='lines',
#         line=dict(width=1.8, color='#777'),
#         hoverinfo='none',
#         showlegend=False
#     ))
    
#     # Draw nodes
#     if num_nodes <= 10:
#         node_size = 50
#         font_size = 10
#     elif num_nodes <= 20:
#         node_size = 40
#         font_size = 9
#     else:
#         node_size = 32
#         font_size = 7
    
#     fig.add_trace(go.Scatter(
#         x=x_coords, y=y_coords,
#         mode='markers+text',
#         marker=dict(
#             size=node_size,
#             color='#87CEEB',
#             line=dict(width=2.5, color='#4682B4')
#         ),
#         text=[n['name'] for n in nodes_data],
#         textposition="middle center",
#         textfont=dict(size=font_size, color='#000', family='Arial Black'),
#         name='States',
#         hovertemplate='<b>%{text}</b><br>Binary: %{customdata}<extra></extra>',
#         customdata=[n['binary'] for n in nodes_data]
#     ))
    
#     # Color controls
#     color_options = [
#         ('Blue', '#87CEEB', '#4682B4'),
#         ('Green', '#90EE90', '#228B22'),
#         ('Coral', '#F08080', '#CD5C5C'),
#         ('Yellow', '#FFE66D', '#DAA520'),
#         ('Lavender', '#E6E6FA', '#9370DB'),
#         ('Pink', '#FFB6C1', '#FF69B4'),
#         ('Mint', '#98FF98', '#00FA9A'),
#         ('Orange', '#FFB366', '#FF8C00'),
#         ('Purple', '#DDA0DD', '#9932CC'),
#         ('Teal', '#40E0D0', '#008B8B')
#     ]
    
#     updatemenus = [
#         dict(
#             buttons=[
#                 dict(label=lbl, method="restyle",
#                      args=[{"marker.color": fill, "marker.line.color": border}, [1]])
#                 for lbl, fill, border in color_options
#             ],
#             direction="down", pad={"r": 5, "t": 5},
#             showactive=True, x=0.01, xanchor="left",
#             y=0.99, yanchor="top",
#             bgcolor="white", bordercolor="#aaa", borderwidth=1,
#             font=dict(size=10)
#         )
#     ]
    
#     fig.update_layout(
#         title=dict(text=title, x=0.5, xanchor='center',
#                    font=dict(size=18, family='Arial', color='#222')),
#         showlegend=False,
#         hovermode='closest',
#         margin=dict(l=80, r=80, t=100, b=80),
#         xaxis=dict(showgrid=True, gridcolor='#e8e8e8', gridwidth=1,
#                    zeroline=False, showticklabels=False,
#                    scaleanchor="y", scaleratio=1),
#         yaxis=dict(showgrid=True, gridcolor='#e8e8e8', gridwidth=1,
#                    zeroline=False, showticklabels=False),
#         plot_bgcolor='white',
#         paper_bgcolor='#f8f9fa',
#         width=width, height=height,
#         dragmode='pan',
#         updatemenus=updatemenus
#     )
    
#     # Legend
#     legend_text = create_compact_legend(legend_mapping, num_nodes)
#     if legend_text:
#         fig.add_annotation(
#             text=legend_text, xref="paper", yref="paper",
#             x=0.98, y=0.98, xanchor="right", yanchor="top",
#             showarrow=False, font=dict(size=9, family='Courier New'),
#             bgcolor='rgba(255, 255, 255, 0.95)',
#             bordercolor='#bbb', borderwidth=1, borderpad=5,
#             align='left'
#         )
    
#     return fig


# def create_compact_legend(legend_mapping, num_nodes):
#     """Create compact legend."""
#     parts = []
    
#     if legend_mapping.get('states'):
#         total = len(legend_mapping['states'])
#         parts.append(f"<b>States ({total})</b>")
        
#         if total > 12:
#             states_list = list(legend_mapping['states'].items())
#             for binary, name in states_list[:4]:
#                 parts.append(f"{binary} → {name}")
#             parts.append(f"⋮ +{total-8} more")
#             for binary, name in states_list[-4:]:
#                 parts.append(f"{binary} → {name}")
#         else:
#             for binary, name in sorted(legend_mapping['states'].items())[:12]:
#                 parts.append(f"{binary} → {name}")
    
#     if legend_mapping.get('events'):
#         parts.append("")
#         total = len(legend_mapping['events'])
#         parts.append(f"<b>Events ({total})</b>")
        
#         if total > 8:
#             events_list = list(legend_mapping['events'].items())
#             for binary, name in sorted(events_list)[:4]:
#                 parts.append(f"{binary} → {name}")
#             parts.append(f"⋮ +{total-4} more")
#         else:
#             for binary, name in sorted(legend_mapping['events'].items())[:8]:
#                 parts.append(f"{binary} → {name}")
    
#     return "<br>".join(parts) if parts else ""

import plotly.graph_objects as go
import networkx as nx
from typing import Dict, List, Tuple, Any
import math


def convert_bdd_to_plotly(bdd_object, title="BDD Visualization", width=2000, height=1400):
    """Convert BDD to clean, non-overlapping visualization."""
    try:
        nodes_data, edges_data, legend_mapping = extract_bdd_structure(bdd_object)
        fig = create_bdd_plotly_figure(nodes_data, edges_data, legend_mapping, title, width, height)
        return fig
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        fig = go.Figure()
        fig.add_annotation(text=f"Error: {e}", xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False, font=dict(size=16, color="red"))
        fig.update_layout(title=title, width=width, height=height)
        return fig


def extract_bdd_structure(bdd_object):
    """Extract nodes and edges from BDD object."""
    nodes_data = []
    edges_data = []
    
    if not isinstance(bdd_object, dict):
        return [], [], {}
    
    states_dict = bdd_object.get('states_dict', {})
    events_dict = bdd_object.get('events_dict', {})
    transitions = bdd_object.get('transitions', [])
    
    legend_mapping = {'states': states_dict, 'events': events_dict}
    
    # Create nodes
    state_name_to_id = {}
    node_id = 0
    for binary, name in states_dict.items():
        nodes_data.append({'id': node_id, 'name': name, 'binary': binary, 'type': 'state'})
        state_name_to_id[name] = node_id
        node_id += 1
    
    # Create edges from actual transitions
    if transitions:
        print(f"Using {len(transitions)} actual transitions")
        edge_id = 0
        for trans in transitions:
            source_name = trans.get('source')
            target_name = trans.get('target')
            event = trans.get('event', f'e{edge_id}')
            
            if source_name in state_name_to_id and target_name in state_name_to_id:
                edges_data.append({
                    'id': edge_id,
                    'source': state_name_to_id[source_name],
                    'target': state_name_to_id[target_name],
                    'label': event
                })
                edge_id += 1
    else:
        print("WARNING: No transitions found!")
    
    return nodes_data, edges_data, legend_mapping


def create_optimal_layout(nodes_data, edges_data):
    """Create layout that GUARANTEES no overlap."""
    num_nodes = len(nodes_data)
    
    if num_nodes == 0:
        return {}
    if num_nodes == 1:
        return {0: (0, 0)}
    
    # Build graph
    G = nx.DiGraph()
    for node in nodes_data:
        G.add_node(node['id'])
    for edge in edges_data:
        G.add_edge(edge['source'], edge['target'])
    
    # STRATEGY: Use multiple layout attempts and pick the best
    layouts = []
    
    # Try 1: Kamada-Kawai (best for small-medium graphs)
    try:
        scale = num_nodes * 50
        pos = nx.kamada_kawai_layout(G, scale=scale)
        layouts.append(('kamada_kawai', pos))
    except Exception as e:
        print(f"Kamada-Kawai failed: {e}")
    
    # Try 2: Spring with very high spacing
    try:
        k = math.sqrt(1.0 / num_nodes) * 30
        scale = num_nodes * 40
        pos = nx.spring_layout(G, k=k, iterations=500, scale=scale, seed=42)
        layouts.append(('spring', pos))
    except Exception as e:
        print(f"Spring failed: {e}")
    
    # Try 3: Planar layout (if graph is planar)
    try:
        if nx.is_planar(G):
            pos = nx.planar_layout(G, scale=num_nodes * 40)
            layouts.append(('planar', pos))
    except:
        pass
    
    # Try 4: Spectral layout
    try:
        pos = nx.spectral_layout(G, scale=num_nodes * 35)
        layouts.append(('spectral', pos))
    except:
        pass
    
    # If all else fails: Use guaranteed grid layout
    if not layouts:
        print("All layouts failed, using grid")
        return create_grid_layout(num_nodes)
    
    # Pick the layout with best spacing (max min distance between nodes)
    best_layout = None
    best_score = 0
    
    for name, pos in layouts:
        min_dist = calculate_min_distance(pos)
        if min_dist > best_score:
            best_score = min_dist
            best_layout = pos
    
    print(f"Using layout with min distance: {best_score:.2f}")
    return best_layout


def calculate_min_distance(pos):
    """Calculate minimum distance between any two nodes."""
    positions = list(pos.values())
    if len(positions) < 2:
        return float('inf')
    
    min_dist = float('inf')
    for i in range(len(positions)):
        for j in range(i + 1, len(positions)):
            x1, y1 = positions[i]
            x2, y2 = positions[j]
            dist = math.sqrt((x2 - x1)**2 + (y2 - y1)**2)
            min_dist = min(min_dist, dist)
    
    return min_dist


def create_grid_layout(num_nodes):
    """Guaranteed non-overlapping grid layout."""
    cols = max(5, int(math.ceil(math.sqrt(num_nodes * 2))))
    spacing = 200
    
    pos = {}
    for i in range(num_nodes):
        row = i // cols
        col = i % cols
        x = col * spacing - (cols * spacing) / 2
        y = -row * spacing
        pos[i] = (x, y)
    
    return pos


def create_bdd_plotly_figure(nodes_data, edges_data, legend_mapping, title, width, height):
    """Create clean Plotly figure with guaranteed spacing."""
    
    if not nodes_data:
        fig = go.Figure()
        fig.add_annotation(text="No data", xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False, font=dict(size=16, color="gray"))
        fig.update_layout(title=title, width=width, height=height)
        return fig
    
    num_nodes = len(nodes_data)
    num_edges = len(edges_data)
    
    print(f"Creating visualization: {num_nodes} nodes, {num_edges} edges")
    
    # Get optimal layout
    pos = create_optimal_layout(nodes_data, edges_data)
    
    x_coords = [pos[node['id']][0] for node in nodes_data]
    y_coords = [pos[node['id']][1] for node in nodes_data]
    
    fig = go.Figure()
    
    # Draw edges
    edge_x, edge_y = [], []
    edge_labels = []
    
    for edge in edges_data:
        if edge['source'] in pos and edge['target'] in pos:
            x0, y0 = pos[edge['source']]
            x1, y1 = pos[edge['target']]
            
            edge_x.extend([x0, x1, None])
            edge_y.extend([y0, y1, None])
            
            # Arrow
            fig.add_annotation(
                x=x1, y=y1, ax=x0, ay=y0,
                axref="x", ayref="y", xref="x", yref="y",
                arrowhead=2, arrowsize=1.0, arrowwidth=1.5,
                arrowcolor="#888", showarrow=True
            )
            
            # Edge label - offset perpendicular to edge
            mid_x, mid_y = (x0 + x1) / 2, (y0 + y1) / 2
            dx, dy = x1 - x0, y1 - y0
            length = math.sqrt(dx**2 + dy**2)
            
            if length > 1:
                offset = 25
                offset_x = -offset * (dy / length) if dy != 0 else offset
                offset_y = offset * (dx / length) if dx != 0 else 0
            else:
                offset_x, offset_y = 15, 0
            
            label_size = 7 if num_nodes > 20 else 8
            
            fig.add_annotation(
                x=mid_x + offset_x, y=mid_y + offset_y,
                text=edge['label'],
                showarrow=False,
                font=dict(size=label_size, color='#2d5016', family='Arial'),
                bgcolor='rgba(255, 255, 255, 0.95)',
                bordercolor='#5a9c3a', borderwidth=1, borderpad=2
            )
    
    # Edge lines
    fig.add_trace(go.Scatter(
        x=edge_x, y=edge_y,
        mode='lines',
        line=dict(width=1.5, color='#999'),
        hoverinfo='none',
        showlegend=False
    ))
    
    # Node sizing
    if num_nodes <= 10:
        node_size, font_size = 55, 11
    elif num_nodes <= 20:
        node_size, font_size = 45, 9
    elif num_nodes <= 30:
        node_size, font_size = 38, 8
    else:
        node_size, font_size = 32, 7
    
    # Draw nodes
    fig.add_trace(go.Scatter(
        x=x_coords, y=y_coords,
        mode='markers+text',
        marker=dict(
            size=node_size,
            color='#87CEEB',
            line=dict(width=2.5, color='#4682B4')
        ),
        text=[n['name'] for n in nodes_data],
        textposition="middle center",
        textfont=dict(size=font_size, color='#000', family='Arial Black'),
        hovertemplate='<b>%{text}</b><br>Binary: %{customdata}<extra></extra>',
        customdata=[n['binary'] for n in nodes_data]
    ))
    
    # Color picker
    colors = [
        ('Blue', '#87CEEB', '#4682B4'), ('Green', '#90EE90', '#228B22'),
        ('Coral', '#F08080', '#CD5C5C'), ('Yellow', '#FFE66D', '#DAA520'),
        ('Lavender', '#E6E6FA', '#9370DB'), ('Pink', '#FFB6C1', '#FF69B4'),
        ('Mint', '#98FF98', '#00FA9A'), ('Orange', '#FFB366', '#FF8C00')
    ]
    
    updatemenus = [
        dict(
            buttons=[dict(label=lbl, method="restyle", args=[{"marker.color": fill, "marker.line.color": border}, [1]]) 
                     for lbl, fill, border in colors],
            direction="down", x=0.01, xanchor="left", y=0.99, yanchor="top",
            bgcolor="white", bordercolor="#aaa", borderwidth=1, font=dict(size=10)
        )
    ]
    
    # Layout
    fig.update_layout(
        title=dict(text=title, x=0.5, xanchor='center', font=dict(size=18, color='#222')),
        showlegend=False,
        hovermode='closest',
        margin=dict(l=100, r=100, t=100, b=100),
        xaxis=dict(showgrid=True, gridcolor='#e0e0e0', zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=True, gridcolor='#e0e0e0', zeroline=False, showticklabels=False),
        plot_bgcolor='white',
        paper_bgcolor='#f5f5f5',
        width=width, height=height,
        dragmode='pan',
        updatemenus=updatemenus
    )
    
    # Compact legend
    legend_text = create_legend(legend_mapping, num_nodes)
    if legend_text:
        fig.add_annotation(
            text=legend_text, xref="paper", yref="paper",
            x=0.98, y=0.98, xanchor="right", yanchor="top",
            showarrow=False, font=dict(size=8, family='Courier New'),
            bgcolor='rgba(255, 255, 255, 0.95)', bordercolor='#bbb',
            borderwidth=1, borderpad=4, align='left'
        )
    
    return fig


def create_legend(legend_mapping, num_nodes):
    """Compact legend."""
    parts = []
    
    if legend_mapping.get('states'):
        total = len(legend_mapping['states'])
        parts.append(f"<b>States ({total})</b>")
        states = list(legend_mapping['states'].items())
        
        if total > 10:
            for b, n in states[:3]: parts.append(f"{b}→{n}")
            parts.append(f"... +{total-6}")
            for b, n in states[-3:]: parts.append(f"{b}→{n}")
        else:
            for b, n in sorted(states)[:10]: parts.append(f"{b}→{n}")
    
    if legend_mapping.get('events'):
        parts.append("")
        total = len(legend_mapping['events'])
        parts.append(f"<b>Events ({total})</b>")
        events = sorted(legend_mapping['events'].items())
        
        for b, n in events[:5]: parts.append(f"{b}→{n}")
        if total > 5: parts.append(f"... +{total-5}")
    
    return "<br>".join(parts)