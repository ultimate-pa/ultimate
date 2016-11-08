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
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.Activator;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public enum MinimizeStates {
		NONE, SINGLE, SINGLE_NODE_MULTI_EDGE, MULTI
	}

	public static final String OPTIMIZE_SBE = "Use SBE for initial RCFG";
	public static final String OPTIMIZE_SBE_REWRITENOTEQUALS = "Rewrite not-equals during SBE";

	/**
	 * Only for termination (i.e., "Büchi" RCFGs)
	 */
	public static final String OPTIMIZE_MAXIMIZE_FINAL_STATES = "Maximize final states";
	public static final String OPTIMIZE_MINIMIZE_STATES = "Minimize states using LBE with the strategy";
	public static final String OPTIMIZE_MINIMIZE_STATES_IGNORE_BLOWUP =
			"Minimize states even if more edges are added than removed.";
	public static final String OPTIMIZE_REMOVE_INFEASIBLE_EDGES = "Remove infeasible edges";

	/**
	 * Only for termination (i.e., "Büchi" RCFGs)
	 */
	public static final String OPTIMIZE_REMOVE_SINK_STATES = "Remove sink states";
	public static final String OPTIMIZE_SIMPLIFY_ASSUMES = "Simplify assume statements";
	public static final String OPTIMIZE_SIMPLIFY_ASSUMES_SBE = "Use SBE during assume simplification";
	public static final String OPTIMIZE_SIMPLIFY_ASSUMES_REWRITENOTEQUALS =
			"Rewrite not equals when simplifying assume statements with SBE";
	public static final String OPTIMIZE_UNTIL_FIXPOINT = "Apply optimizations until nothing changes";
	public static final String OPTIMIZE_MAX_ITERATIONS =
			"Iterate optimizations for n times (<=0 means until nothing changes)";

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>("RCFG Optimizations", "", PreferenceType.Label),
				new UltimatePreferenceItem<>(OPTIMIZE_SBE, Boolean.FALSE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_SBE_REWRITENOTEQUALS, Boolean.FALSE, PreferenceType.Boolean),

				new UltimatePreferenceItem<>("Product Optimizations", "", PreferenceType.Label),
				new UltimatePreferenceItem<>(OPTIMIZE_MAXIMIZE_FINAL_STATES, Boolean.TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_MINIMIZE_STATES, MinimizeStates.MULTI, PreferenceType.Combo,
						MinimizeStates.values()),
				new UltimatePreferenceItem<>(OPTIMIZE_MINIMIZE_STATES_IGNORE_BLOWUP, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_REMOVE_INFEASIBLE_EDGES, Boolean.TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_REMOVE_SINK_STATES, Boolean.TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_SIMPLIFY_ASSUMES, Boolean.FALSE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_SIMPLIFY_ASSUMES_SBE, Boolean.FALSE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_SIMPLIFY_ASSUMES_REWRITENOTEQUALS, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_UNTIL_FIXPOINT, Boolean.TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(OPTIMIZE_MAX_ITERATIONS, 0, PreferenceType.Integer),

		};
	}
}
