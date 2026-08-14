/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.preferences;

import org.eclipse.swt.graphics.RGB;

/**
 * Preference values for the SWT visualization plug-in.
 */
public class SwtPreferenceValues {

	// LABELS (used as preference keys)
	public static final String LABEL_COLOR_NODE = "Node color:";
	public static final String LABEL_COLOR_NODE_PICKED = "Picked node color:";
	public static final String LABEL_COLOR_BACKGROUND = "Background color:";
	public static final String LABEL_EDGE_LABELS = "Edge labels:";
	public static final String LABEL_LAYOUT = "Default graph layout:";
	public static final String LABEL_WHICH_MODEL = "Which models should be visualized?";

	// DEFAULT VALUES
	public static final RGB VALUE_COLOR_NODE_DEFAULT = new RGB(180, 220, 255);
	public static final RGB VALUE_COLOR_NODE_PICKED_DEFAULT = new RGB(255, 235, 100);
	public static final RGB VALUE_COLOR_BACKGROUND_DEFAULT = new RGB(255, 255, 255);
	public static final EdgeLabels VALUE_EDGE_LABELS_DEFAULT = EdgeLabels.None;
	public static final String VALUE_LAYOUT_DEFAULT = "TreeLayout";

	public enum EdgeLabels {
		None, Text
	}
}
