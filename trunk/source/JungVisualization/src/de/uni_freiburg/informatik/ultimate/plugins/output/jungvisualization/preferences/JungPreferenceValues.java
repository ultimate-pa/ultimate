package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;

/**
 * Contains values, labels, default values for the fields of the JungVisualization preference page.
 *
 * @author lena
 *
 */
public class JungPreferenceValues {
	
	public static ScopedPreferenceStore Preference = new ScopedPreferenceStore(
			InstanceScope.INSTANCE, Activator.PLUGIN_ID);
	
    //NAMES
	public static final String NAME_PATH = "pathPreference";
	public static final String NAME_ANNOTATED_EDGES = "annotatedEdgesPreference";
	public static final String NAME_ANNOTATED_NODES = "annotatedNodesPreference";
	public static final String NAME_LAYOUT = "layoutPreference";
	
	public static final String NAME_COLOR_NODE = "colorForNodePreference";
	public static final String NAME_COLOR_NODE_PICKED = "colorForNodePickedPreference";
	public static final String NAME_COLOR_BACKGROUND = "colorForBackgroundPreference";
	
	public static final String NAME_SHAPE_NODE = "shapeForNodePreference";
	
	
	//DEFAULT VALUES
	public static final String VALUE_PATH_DEFAULT = ".";
	public static final boolean VALUE_ANNOTATED_EDGES_DEFAULT = false;
	public static final boolean VALUE_ANNOTATED_NODES_DEFAULT = true;
	public static final String VALUE_LAYOUT_DEFAULT = "TreeLayout";
	
	public static final RGB VALUE_COLOR_NODE_DEFAULT = new RGB(103, 209, 248); //HTML:67d1f8, HSV:196,58,97
	public static final RGB VALUE_COLOR_NODE_PICKED_DEFAULT = new RGB(246, 239, 47);
	public static final RGB VALUE_COLOR_BACKGROUND_DEFAULT = new RGB(255, 255, 255); //HTML:ffff, HSV:0,0,100
	
	public static final String VALUE_SHAPE_NODE_DEFAULT = "RoundRectangle";
	
	
	//LABELS
	public static final String LABEL_PATH = "SVG Export directory:";
	public static final String LABEL_ANNOTATED_EDGES = "Annotate edges";
	public static final String LABEL_ANNOTATED_NODES = "Annotate nodes";
	public static final String LABEL_LAYOUT = "Default graph layout:";
	
	public static final String LABEL_COLOR_NODE = "Node color:";
	public static final String LABEL_COLOR_NODE_PICKED = "Picked node color:";
	public static final String LABEL_COLOR_BACKGROUND = "Background color:";
	
	public static final String LABEL_SHAPE_NODE = "Choose node shape:";	
	
}
