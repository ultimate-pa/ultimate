/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;

/**
 * Initializer and container of preferences for the view abstraction plugin.
 */
public class ViewAbstractionPreferenceInitializer extends UltimatePreferenceInitializer {
	public static final String LABEL_MIN_LEVEL = "Minimum view abstraction level";
	private static final int DEF_MIN_LEVEL = 1;

	public static final String LABEL_MAX_LEVEL = "Maximum view abstraction level";
	private static final String DESC_MAX_LEVEL = "A value of 0 or below means there is no maximum.";
	private static final int DEF_MAX_LEVEL = 0;

	public static final String LABEL_ENABLE_SLEEP_SETS = "Enable sleep set reduction";
	private static final boolean DEF_ENABLE_SLEEP_SETS = false;

	public static final String LABEL_ENABLE_PERSISTENT_SETS = "Enable persistent set reduction";
	private static final boolean DEF_ENABLE_PERSISTENT_SETS = false;

	public static final String LABEL_USE_SEMICOMMUTATIVITY = "Use semi-commutativity for reduction";

	public ViewAbstractionPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "View Abstraction");
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new BaseUltimatePreferenceItem[] {
				new UltimatePreferenceItem<>(LABEL_MIN_LEVEL, DEF_MIN_LEVEL, PreferenceType.Integer, false),
				new UltimatePreferenceItem<>(LABEL_MAX_LEVEL, DEF_MAX_LEVEL, DESC_MAX_LEVEL, PreferenceType.Integer),

				// reduction techniques
				new UltimatePreferenceItem<>(LABEL_ENABLE_SLEEP_SETS, DEF_ENABLE_SLEEP_SETS, PreferenceType.Boolean,
						false),
				new UltimatePreferenceItem<>(LABEL_ENABLE_PERSISTENT_SETS, DEF_ENABLE_PERSISTENT_SETS,
						PreferenceType.Boolean),

				// independence settings
				new UltimatePreferenceItem<>(LABEL_USE_SEMICOMMUTATIVITY,
						IndependenceSettings.DEFAULT_USE_SEMICOMMUTATIVITY, PreferenceType.Boolean, false),

		};
	}
}
