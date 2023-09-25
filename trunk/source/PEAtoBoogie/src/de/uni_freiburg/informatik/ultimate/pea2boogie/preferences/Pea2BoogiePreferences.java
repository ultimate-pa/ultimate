/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Pea2BoogiePreferences extends UltimatePreferenceInitializer {

	public static final String LABEL_TRANSFOMER_MODE = "PEA Transformation Mode";
	public static final PEATransformerMode TRANSFOMER_MODE = PEATransformerMode.REQ_CHECK;
	private static final String DESC_TRANSFOMER_MODE =
			"Switches between checking requirements and generating tests for requirements.";

	public static final String LABEL_CHECK_VACUITY = "Check vacuity";
	private static final boolean DEF_CHECK_VACUITY = true;
	private static final String DESC_CHECK_VACUITY = null;

	public static final String LABEL_CHECK_CONSISTENCY = "Check consistency";
	private static final boolean DEF_CHECK_CONSISTENCY = true;
	private static final String DESC_CHECK_CONSISTENCY = null;

	public static final String LABEL_CHECK_RT_INCONSISTENCY = "Check rt-inconsistency";
	private static final boolean DEF_CHECK_RT_INCONSISTENCY = true;
	private static final String DESC_CHECK_RT_INCONSISTENCY = null;

	public static final String LABEL_USE_EPSILON = "Use epsilon transformation during rt-inconsistency check";
	private static final boolean DEF_USE_EPSILON = true;
	private static final String DESC_USE_EPSILON = null;

	public static final String LABEL_RT_INCONSISTENCY_RANGE = "Rt-inconsistency range";
	private static final int DEF_RT_INCONSISTENCY_RANGE = 2;
	private static final String DESC_RT_INCONSISTENCY_RANGE =
			"How many requirements should be checked for rt-inconsistency at the same time? "
					+ "Allows only positive integer values. " + "Note: This value increases the runtime exponentially!"
					+ "Note: A value of one can be used to check rt-inconsistency with invariants.";
	public static final String LABEL_REPORT_TRIVIAL_RT_CONSISTENCY = "Report trivial rt-consistency";
	private static final boolean DEF_REPORT_TRIVIAL_RT_CONSISTENCY = false;
	private static final String DESC_REPORT_TRIVIAL_RT_CONSISTENCY =
			"Generate a result even if rt-consistency is shown during the generation of the assertion";

	public static final String LABEL_RT_INCONSISTENCY_USE_ALL_INVARIANTS =
			"Always use all invariants during rt-inconsistency checks";
	private static final boolean DEF_RT_INCONSISTENCY_USE_ALL_INVARIANTS = true;
	private static final String DESC_RT_INCONSISTENCY_USE_ALL_INVARIANTS =
			"This setting controls whether invariant requirements are included in every rt-inconsistency check or if they"
					+ " are treated as separate requirements. If enabled, each rt-inconsistency check is of the form "
					+ "Invariants ∧ (check over all remaining requirements). If disabled, invariants are not treated separately.";

	public static final String LABEL_GUESS_IN_OUT =
			"Use heuristic to find input/output definitions (if none are given)";
	private static final boolean DEF_GUESS_IN_OUT = true;
	private static final String DESC_GUESS_IN_OUT = "If there is no explicit definition of inputs, outputs and internal"
			+ "variables in the Requirements file (i.e. only inputs), use the follwing heuristics:"
			+ "Every variable that is never influenced by a requirement is an input"
			+ "Every variable that is never used in the precondition of a requirement is an output"
			+ "The rest is internal. Note: this is the most conservative assignment suited for demos, but "
			+ " usually not helpful in the wild";

	public static final String LABEL_GUESS_INITIAL = "Guess initial output assignment";
	private static final boolean DEF_GUESS_INITIAL = false;
	private static final String DESC_GUESS_INITIAL = "Allow for the test generator to initially guess an arbitrary"
			+ "value for all output variables. This shall help finding tests for systems with feedback loops i.e. that "
			+ "require a previosu state to determine the successor state. Note: this will only work for the very first"
			+ "step independend of length or usefulness.";

	public enum PEATransformerMode {
		REQ_CHECK, REQ_TEST, REQ_RED
	}

	public Pea2BoogiePreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {

			new UltimatePreferenceItem<>(LABEL_TRANSFOMER_MODE, TRANSFOMER_MODE, DESC_TRANSFOMER_MODE,
					PreferenceType.Combo, PEATransformerMode.values()),
			new UltimatePreferenceItem<>(LABEL_CHECK_VACUITY, DEF_CHECK_VACUITY, DESC_CHECK_VACUITY,
					PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_CHECK_CONSISTENCY, DEF_CHECK_CONSISTENCY, DESC_CHECK_CONSISTENCY,
					PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_CHECK_RT_INCONSISTENCY, DEF_CHECK_RT_INCONSISTENCY,
					DESC_CHECK_RT_INCONSISTENCY, PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_USE_EPSILON, DEF_USE_EPSILON, DESC_USE_EPSILON,
					PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_REPORT_TRIVIAL_RT_CONSISTENCY, DEF_REPORT_TRIVIAL_RT_CONSISTENCY,
					DESC_REPORT_TRIVIAL_RT_CONSISTENCY, PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_RT_INCONSISTENCY_RANGE, DEF_RT_INCONSISTENCY_RANGE,
					DESC_RT_INCONSISTENCY_RANGE, PreferenceType.Integer,
					IUltimatePreferenceItemValidator.ONLY_POSITIVE),
			new UltimatePreferenceItem<>(LABEL_RT_INCONSISTENCY_USE_ALL_INVARIANTS,
					DEF_RT_INCONSISTENCY_USE_ALL_INVARIANTS, DESC_RT_INCONSISTENCY_USE_ALL_INVARIANTS,
					PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_GUESS_IN_OUT, DEF_GUESS_IN_OUT, DESC_GUESS_IN_OUT,
					PreferenceType.Boolean),
			new UltimatePreferenceItem<>(LABEL_GUESS_INITIAL, DEF_GUESS_INITIAL, DESC_GUESS_INITIAL,
					PreferenceType.Boolean) };
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}
}
