/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import org.eclipse.jface.resource.StringConverter;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.ITool.ModelQuery;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues.EdgeLabels;

/**
 * 
 * @author dietsch
 * 
 */
public class JungPreferenceInitializer extends UltimatePreferenceInitializer {

	public JungPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_PATH,
						JungPreferenceValues.VALUE_PATH_DEFAULT, PreferenceType.Directory),
				new UltimatePreferenceItem<EdgeLabels>(JungPreferenceValues.LABEL_ANNOTATED_EDGES,
						JungPreferenceValues.VALUE_ANNOTATED_EDGES_DEFAULT, PreferenceType.Combo, EdgeLabels.values()),
				new UltimatePreferenceItem<Boolean>(JungPreferenceValues.LABEL_ANNOTATED_NODES,
						JungPreferenceValues.VALUE_ANNOTATED_NODES_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_LAYOUT,
						JungPreferenceValues.VALUE_LAYOUT_DEFAULT, PreferenceType.Combo, new String[] { "FRLayout",
								"FRLayout2", "ISOMLayout", "KKLayout", "TreeLayout" }),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_BACKGROUND,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_BACKGROUND_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_NODE,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_NODE_DEFAULT), PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_NODE_PICKED,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_NODE_PICKED_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_SHAPE_NODE,
						JungPreferenceValues.VALUE_SHAPE_NODE_DEFAULT, PreferenceType.Combo, new String[] {
								"RoundRectangle", "Rectangle", "Ellipse" }),
				new UltimatePreferenceItem<ModelQuery>(JungPreferenceValues.LABEL_WHICH_MODEL, ModelQuery.LAST,
						PreferenceType.Combo, ModelQuery.values()) 
						};
	}
}
