import plotly.graph_objects as go
import plotly.offline as pyo
import webbrowser
import os
import tempfile
from datetime import datetime
from bdd_to_plotly import convert_bdd_to_plotly


def plot_bdd(bdd_object, title="BDD Visualization", width=1200, height=800, show_browser=True, save_html=False, output_file=None):
    try:
        print(f"🎯 Creating BDD visualization: {title}")
        
        # Convert BDD to Plotly figure
        fig = convert_bdd_to_plotly(bdd_object, title, width, height)
        
        # Display in browser if requested
        if show_browser:
            display_in_browser(fig, title)
        
        # Save to HTML file if requested
        if save_html:
            if output_file is None:
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                output_file = f"bdd_visualization_{timestamp}.html"
            save_visualization(fig, output_file)
        
        return fig
        
    except Exception as e:
        print(f"❌ Error in BDD visualization: {e}")
        # Return error figure
        fig = go.Figure()
        fig.add_annotation(
            text=f"Visualization Error: {str(e)}",
            xref="paper", yref="paper",
            x=0.5, y=0.5, showarrow=False,
            font=dict(size=16, color="red")
        )
        fig.update_layout(title=title, width=width, height=height)
        return fig


def display_in_browser(fig, title="BDD Visualization"):
    try:
        # Create temporary HTML file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False) as tmp_file:
            # Write the figure to HTML
            pyo.plot(fig, filename=tmp_file.name, auto_open=False)
            
            # Open in browser
            webbrowser.open(f'file://{tmp_file.name}')
            print(f"🌐 Opening visualization in browser: {title}")
            
    except Exception as e:
        print(f"❌ Error displaying in browser: {e}")


def save_visualization(fig, output_file):
    """
    Save the Plotly figure to an HTML file.
    
    Args:
        fig: Plotly figure object
        output_file: Path to output HTML file
    """
    try:
        # Ensure output directory exists
        os.makedirs(os.path.dirname(output_file) if os.path.dirname(output_file) else '.', exist_ok=True)
        
        # Save the figure
        pyo.plot(fig, filename=output_file, auto_open=False)
        print(f"💾 Visualization saved to: {output_file}")
        
    except Exception as e:
        print(f"❌ Error saving visualization: {e}")


def validate_bdd_object(bdd_object):
    """
    Validate that a BDD object has the required structure for visualization.
    
    Args:
        bdd_object: Object to validate
        
    Returns:
        tuple: (is_valid, error_message)
    """
    try:
        # Check if object has required attributes
        if not isinstance(bdd_object, dict):
            return False, "Object is not a dictionary"
        
        if 'states_dict' not in bdd_object:
            return False, "Missing 'states_dict' attribute"
        
        if 'events_dict' not in bdd_object:
            return False, "Missing 'events_dict' attribute"
        
        return True, "Valid BDD object"
        
    except Exception as e:
        return False, f"Validation error: {e}"