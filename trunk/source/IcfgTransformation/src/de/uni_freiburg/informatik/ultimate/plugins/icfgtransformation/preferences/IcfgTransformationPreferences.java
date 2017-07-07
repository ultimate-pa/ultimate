/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRTransformer.FastUPRReplacementMethod;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation.Activator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformationPreferences extends UltimatePreferenceInitializer {

	public static final String LABEL_TRANSFORMATION_TYPE = "TransformationType";
	private static final String DESC_TRANSFORMATION_TYPE = "";

	public static final String LABEL_FASTUPR_MODE = "FastUPR replacement mode";
	private static final String DESC_FASTUPR_MODE =
			"REPLACE_LOOP_EDGE replaces the loop edge in place (might be slow), "
					+ "REPLACE_EXIT_EDGE replaces the exit edge with a merge of the loop edge and the exit edge "
					+ "(unknown behavior for already transformed Icfg - "
					+ "e.g. if the exit edge was already merged with other edges)";

	/**
	 * Select which transformation should be performed by this plugin.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum TransformationTestType {
		MAP_ELIMINATION_NO_EQUALITY,

		MAP_ELIMINATION_EQUALITY,

		REMOVE_DIV_MOD,

		MODULO_NEIGHBOR,

		LOOP_ACCELERATION_EXAMPLE,

		LOOP_ACCELERATION_BIESENBACH,

		LOOP_ACCELERATION_MOHR,

		LOOP_ACCELERATION_WOELFING,

		LOOP_ACCELERATION_FASTUPR,

		LOOP_ACCELERATION_WERNER,

		LOOP_ACCELERATION_AHMED,

		HEAP_SEPARATOR

	}

	/**
	 * Default constructor.
	 */
	public IcfgTransformationPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {

				new UltimatePreferenceItem<>(LABEL_TRANSFORMATION_TYPE,
						TransformationTestType.LOOP_ACCELERATION_EXAMPLE, DESC_TRANSFORMATION_TYPE,
						PreferenceType.Combo, TransformationTestType.values()),
				new UltimatePreferenceItem<>(LABEL_FASTUPR_MODE, FastUPRReplacementMethod.REPLACE_EXIT_EDGE,
						DESC_FASTUPR_MODE, PreferenceType.Combo, FastUPRReplacementMethod.values()),

		};
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}
}
