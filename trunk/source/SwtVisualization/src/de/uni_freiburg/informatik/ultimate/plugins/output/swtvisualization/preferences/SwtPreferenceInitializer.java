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

import org.eclipse.jface.resource.StringConverter;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.ITool.ModelQuery;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.preferences.SwtPreferenceValues.EdgeLabels;

/**
 * Preference initializer for the SWT visualization plug-in.
 */
public class SwtPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String KEY_WHICH_MODEL = SwtPreferenceValues.LABEL_WHICH_MODEL;

	public SwtPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_COLOR_BACKGROUND,
						StringConverter.asString(SwtPreferenceValues.VALUE_COLOR_BACKGROUND_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_COLOR_NODE,
						StringConverter.asString(SwtPreferenceValues.VALUE_COLOR_NODE_DEFAULT), PreferenceType.Color),
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_COLOR_NODE_PICKED,
						StringConverter.asString(SwtPreferenceValues.VALUE_COLOR_NODE_PICKED_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_EDGE_LABELS,
						SwtPreferenceValues.VALUE_EDGE_LABELS_DEFAULT, PreferenceType.Combo, EdgeLabels.values()),
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_LAYOUT,
						SwtPreferenceValues.VALUE_LAYOUT_DEFAULT, PreferenceType.Combo,
						new String[] { "TreeLayout", "LayeredLayout" }),
				new UltimatePreferenceItem<>(SwtPreferenceValues.LABEL_WHICH_MODEL, ModelQuery.LAST,
						PreferenceType.Combo, ModelQuery.values()) };
	}
}
