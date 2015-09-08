/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jelena Barth
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2010-2015 pashko
 * 
 * This file is part of the ULTIMATE JungVisualization plug-in.
 * 
 * The ULTIMATE JungVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JungVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JungVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JungVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE JungVisualization plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;

/**
 * Contains values, labels, default values for the fields of the
 * JungVisualization preference page.
 * 
 * @author lena
 * 
 */
public class JungPreferenceValues {

	public static ScopedPreferenceStore Preference = new ScopedPreferenceStore(InstanceScope.INSTANCE,
			Activator.PLUGIN_ID);

	// NAMES
	public static final String NAME_PATH = "pathPreference";
	public static final String NAME_ANNOTATED_EDGES = "annotatedEdgesPreference";
	public static final String NAME_ANNOTATED_NODES = "annotatedNodesPreference";
	public static final String NAME_LAYOUT = "layoutPreference";

	public static final String NAME_COLOR_NODE = "colorForNodePreference";
	public static final String NAME_COLOR_NODE_PICKED = "colorForNodePickedPreference";
	public static final String NAME_COLOR_BACKGROUND = "colorForBackgroundPreference";

	public static final String NAME_SHAPE_NODE = "shapeForNodePreference";

	// DEFAULT VALUES
	public static final String VALUE_PATH_DEFAULT = ".";
	public static final EdgeLabels VALUE_ANNOTATED_EDGES_DEFAULT = EdgeLabels.None;
	public static final boolean VALUE_ANNOTATED_NODES_DEFAULT = true;
	public static final String VALUE_LAYOUT_DEFAULT = "TreeLayout";

	public static final RGB VALUE_COLOR_NODE_DEFAULT = new RGB(103, 209, 248); // HTML:67d1f8,
																				// HSV:196,58,97
	public static final RGB VALUE_COLOR_NODE_PICKED_DEFAULT = new RGB(246, 239, 47);
	public static final RGB VALUE_COLOR_BACKGROUND_DEFAULT = new RGB(255, 255, 255); // HTML:ffff,
																						// HSV:0,0,100

	public static final String VALUE_SHAPE_NODE_DEFAULT = "RoundRectangle";

	public enum EdgeLabels {
		None, Text, Hashcode
	}

	// LABELS
	public static final String LABEL_PATH = "SVG Export directory:";
	public static final String LABEL_ANNOTATED_EDGES = "Annotate edges";
	public static final String LABEL_ANNOTATED_NODES = "Annotate nodes";
	public static final String LABEL_LAYOUT = "Default graph layout:";

	public static final String LABEL_COLOR_NODE = "Node color:";
	public static final String LABEL_COLOR_NODE_PICKED = "Picked node color:";
	public static final String LABEL_COLOR_BACKGROUND = "Background color:";

	public static final String LABEL_SHAPE_NODE = "Choose node shape:";
	
	public static final String LABEL_WHICH_MODEL = "Which models should be visualized?";

}
