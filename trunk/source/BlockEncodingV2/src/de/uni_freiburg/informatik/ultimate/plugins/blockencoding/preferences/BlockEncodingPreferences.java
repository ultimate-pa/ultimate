/*
 * Copyright (C) 2015-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
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

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BlockEncodingPreferences extends UltimatePreferenceInitializer {

	public enum MinimizeStates {
		NONE, SINGLE, SINGLE_NODE_MULTI_EDGE, MULTI
	}

	private static final Boolean PRE_SBE_DEF = Boolean.FALSE;
	private static final boolean FXP_MAXIMIZE_FINAL_STATES_DEF = true;
	private static final boolean FXP_REMOVE_INFEASIBLE_EDGES_DEF = true;
	private static final boolean FXP_REMOVE_SINK_STATES_DEF = true;
	private static final boolean FXP_INTERPROCEDURAL_COMPOSITION_DEF = true;
	private static final boolean FXP_UNTIL_FIXPOINT_DEF = true;
	private static final boolean POST_USE_PARALLEL_COMPOSITION_DEF = true;
	private static final boolean PRE_REWRITENOTEQUALS_DEF = false;
	private static final boolean FXP_MINIMIZE_STATES_IGNORE_BLOWUP_DEF = false;
	private static final boolean POST_SIMPLIFY_TRANSITIONS_DEF = false;
	private static final MinimizeStates FXP_MINIMIZE_STATES_DEF = MinimizeStates.MULTI;
	private static final int FXP_MAX_ITERATIONS_DEF = 0;

	public static final String PLUGIN_ID = Activator.PLUGIN_ID;

	public static final String PRE_SBE = "Use SBE";
	public static final String PRE_REWRITENOTEQUALS = "Rewrite not-equals";

	public static final String FXP_MAXIMIZE_FINAL_STATES = "Maximize final states";

	public static final String FXP_MINIMIZE_STATES = "Minimize states using LBE with the strategy";
	public static final String FXP_MINIMIZE_STATES_IGNORE_BLOWUP =
			"Minimize states even if more edges are added than removed.";
	public static final String FXP_REMOVE_INFEASIBLE_EDGES = "Remove infeasible edges";
	public static final String FXP_REMOVE_SINK_STATES = "Remove sink states";
	public static final String FXP_UNTIL_FIXPOINT = "Apply optimizations until nothing changes";
	public static final String FXP_MAX_ITERATIONS =
			"Iterate optimizations for n times (<=0 means until nothing changes)";
	public static final String FXP_INTERPROCEDURAL_COMPOSITION = "Create interprocedural compositions";

	public static final String POST_USE_PARALLEL_COMPOSITION = "Create parallel compositions if possible";
	public static final String POST_SIMPLIFY_TRANSITIONS = "Simplify transitions";

	private static final String PRE_SBE_DESC = null;
	private static final String PRE_SBE_REWRITENOTEQUALS_DESC = null;

	private static final String FXP_MAX_ITERATIONS_DESC = null;
	private static final String FXP_UNTIL_FIXPOINT_DESC = null;
	private static final String FXP_REMOVE_SINK_STATES_DESC = null;
	private static final String FXP_REMOVE_INFEASIBLE_EDGES_DESC = null;
	private static final String FXP_INTERPROCEDURAL_COMPOSITION_DESC = null;
	private static final String FXP_MINIMIZE_STATES_IGNORE_BLOWUP_DESC = null;
	private static final String FXP_MINIMIZE_STATES_DESC = null;
	private static final String FXP_MAXIMIZE_FINAL_STATES_DESC = null;

	private static final String POST_USE_PARALLEL_COMPOSITION_DESC = null;
	private static final String POST_SIMPLIFY_TRANSITIONS_DESC = null;

	public BlockEncodingPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>("Pre-processing", "", PreferenceType.Label),
				new UltimatePreferenceItem<>(PRE_SBE, PRE_SBE_DEF, PRE_SBE_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(PRE_REWRITENOTEQUALS, PRE_REWRITENOTEQUALS_DEF,
						PRE_SBE_REWRITENOTEQUALS_DESC, PreferenceType.Boolean),

				new UltimatePreferenceItem<>("Iterative encodings", "", PreferenceType.Label),
				new UltimatePreferenceItem<>(FXP_MAXIMIZE_FINAL_STATES, FXP_MAXIMIZE_FINAL_STATES_DEF,
						FXP_MAXIMIZE_FINAL_STATES_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_MINIMIZE_STATES, FXP_MINIMIZE_STATES_DEF, FXP_MINIMIZE_STATES_DESC,
						PreferenceType.Combo, MinimizeStates.values()),
				new UltimatePreferenceItem<>(FXP_MINIMIZE_STATES_IGNORE_BLOWUP, FXP_MINIMIZE_STATES_IGNORE_BLOWUP_DEF,
						FXP_MINIMIZE_STATES_IGNORE_BLOWUP_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_REMOVE_INFEASIBLE_EDGES, FXP_REMOVE_INFEASIBLE_EDGES_DEF,
						FXP_REMOVE_INFEASIBLE_EDGES_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_REMOVE_SINK_STATES, FXP_REMOVE_SINK_STATES_DEF,
						FXP_REMOVE_SINK_STATES_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_INTERPROCEDURAL_COMPOSITION, FXP_INTERPROCEDURAL_COMPOSITION_DEF,
						FXP_INTERPROCEDURAL_COMPOSITION_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_UNTIL_FIXPOINT, FXP_UNTIL_FIXPOINT_DEF, FXP_UNTIL_FIXPOINT_DESC,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(FXP_MAX_ITERATIONS, FXP_MAX_ITERATIONS_DEF, FXP_MAX_ITERATIONS_DESC,
						PreferenceType.Integer),

				new UltimatePreferenceItem<>("Post processing", "", PreferenceType.Label),
				new UltimatePreferenceItem<>(POST_USE_PARALLEL_COMPOSITION, POST_USE_PARALLEL_COMPOSITION_DEF,
						POST_USE_PARALLEL_COMPOSITION_DESC, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(POST_SIMPLIFY_TRANSITIONS, POST_SIMPLIFY_TRANSITIONS_DEF,
						POST_SIMPLIFY_TRANSITIONS_DESC, PreferenceType.Boolean),

		};
	}
}
