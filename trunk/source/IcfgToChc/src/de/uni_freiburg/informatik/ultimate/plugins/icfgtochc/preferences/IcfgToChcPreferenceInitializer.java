/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ConcurrencyMode;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences.SpecMode;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcPreferenceInitializer extends UltimatePreferenceInitializer {

	// SETTINGS FOR CONCURRENT PROGRAMS
	// ------------------------------------------------------------------------

	public static final String LABEL_CONCURRENCY_MODE = "Concurrency mode";
	public static final String DESC_CONCURRENCY_MODE =
			"Whether the program starts as a single thread, which may dynamically fork and join new threads, "
					+ "or as a parametric program, i.e., with an unbounded number of threads, "
					+ "all starting at once.";
	public static final ConcurrencyMode DEF_CONCURRENCY_MODE = ConcurrencyMode.PARAMETRIC;

	public static final String LABEL_HAS_PRECONDITION = "Assume program has a precondition";
	public static final String DESC_HAS_PRECONDITION =
			"Use if the thread templates have a precondition annotated as a 'free requires'.";
	public static final boolean DEF_HAS_PRECONDITION = true;

	public static final String LABEL_SPEC_MODE = "Specification mode";
	public static final String DESC_SPEC_MODE = "Describes how the specification for the program is given.";
	public static final SpecMode DEF_SPEC_MODE = SpecMode.POSTCONDITION;

	// TODO Introduce PreferenceType.List?
	public static final String LABEL_PARAMETRIC_TEMPLATES = "Templates for parametric program";
	private static final String DESC_PARAMETRIC_TEMPLATES = "Comma-separated list of procedures denoting thread "
			+ "templates of the parametric program. Leave empty for default behaviour (i.e., single template given "
			+ "by ULTIMATE.start in Boogie, main in C).";
	private static final String DEF_PARAMETRIC_TEMPLATES = "";

	public static final String LABEL_PARAMETRIC_SINGLE_THREADS = "Single-instance threads";
	private static final String DESC_PARAMETRIC_SINGLE_THREADS =
			"Comma-separated list of procedures for which a single thread is running in a parametric program.";
	private static final String DEF_PARAMETRIC_SINGLE_THREADS = "";

	// SETTINGS FOR THREAD-MODULAR PROOFS
	// ------------------------------------------------------------------------

	public static final String LABEL_THREADMODULAR_LEVEL = "Thread-Modular Proof Level";
	private static final String DESC_THREADMODULAR_LEVEL =
			"The level at which thread-modular proofs should be computed";
	private static final int DEF_THREADMODULAR_LEVEL = 2;

	public static final String LABEL_SYMMETRY_CLAUSES = "Use symmetry clauses";
	private static final boolean DEF_SYMMETRY_CLAUSES = false;

	// TODO Currently unused
	public static final String LABEL_EXPLICIT_LOCATIONS = "Encode control locations explicitly";
	private static final String DESC_EXPLICIT_LOCATIONS = "Control locations can be encoded symbolically "
			+ "(as CHC variables), or explicitly (by using different predicate symbols).";
	private static final boolean DEF_EXPLICIT_LOCATIONS = false;

	public static final String LABEL_LIPTON_REDUCTION = "Apply Lipton reduction";
	private static final String DESC_LIPTON_REDUCTION = "If enabled, Lipton reduction is applied to simplify thread "
			+ "templates, before a thread-modular proof is computed.";
	private static final boolean DEF_LIPTON_REDUCTION = false;

	public static final String LABEL_SKIP_ASSERT_EDGES = "Skip assert edges";
	private static final String DESC_SKIP_ASSERT_EDGES = "If enabled, we do not directly encode unreachability of "
			+ "error locations. Instead, the assertion condition is part of the safety clause.";
	private static final boolean DEF_SKIP_ASSERT_EDGES = true;

	// SETTINGS FOR SLEEP SET REDUCTION
	// ------------------------------------------------------------------------

	public static final String LABEL_SLEEP_SET_REDUCTION = "Enable sleep set reduction";
	private static final String DESC_SLEEP_SET_REDUCTION = "If enabled, symbolic sleep set reduction is applied to the "
			+ "program. This allows for more programs to be proven correct.";
	private static final boolean DEF_SLEEP_SET_REDUCTION = true;

	public static final String LABEL_BREAK_PREFORDER_SYMMETRY = "Break symmetry of preference order";
	private static final String DESC_BREAK_PREFORDER_SYMMETRY = "A straightforward encoding forces proofs to consider "
			+ "all symmetric preference orders. If we break symmetry, more proofs are accepted.";
	private static final boolean DEF_BREAK_PREFORDER_SYMMETRY = true;

	// TODO Currently unused
	public static final String LABEL_EXPLICIT_SLEEP = "Encode sleep sets explicitly";
	private static final String DESC_EXPLICIT_SLEEP = "Sleep sets can be encoded symbolically (as CHC variables), "
			+ "or explicitly (by using different predicate symbols).";
	private static final boolean DEF_EXPLICIT_SLEEP = false;

	public static final String LABEL_PREFERENCE_ORDER = "Preference order used for reduction";
	private static final PreferenceOrder DEF_PREFERENCE_ORDER = PreferenceOrder.SEQ_COMP;

	public static final String LABEL_CONDITIONAL_INDEPENDENCE = "Conditional Independence";
	private static final ConditionalIndependence DEF_CONDITIONAL_INDEPENDENCE = ConditionalIndependence.OFF;

	public static final String LABEL_SEMICOMMUTATIVITY = "Use semi-commutativity";
	private static final boolean DEF_SEMICOMMUTATIVITY = true;

	public enum PreferenceOrder {
		SEQ_COMP, LOCKSTEP
	}

	public enum ConditionalIndependence {
		OFF, PRECOMPUTED_CONDITIONS
	}

	/**
	 * Default constructor.
	 */
	public IcfgToChcPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new BaseUltimatePreferenceItem[] {
				// Settings for concurrent programs
				new UltimatePreferenceItem<>(LABEL_CONCURRENCY_MODE, DEF_CONCURRENCY_MODE, DESC_CONCURRENCY_MODE,
						PreferenceType.Combo, ConcurrencyMode.values()),
				new UltimatePreferenceItem<>(LABEL_HAS_PRECONDITION, DEF_HAS_PRECONDITION, DESC_HAS_PRECONDITION,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SPEC_MODE, DEF_SPEC_MODE, DESC_SPEC_MODE, PreferenceType.Combo,
						SpecMode.values()),
				new UltimatePreferenceItem<>(LABEL_PARAMETRIC_TEMPLATES, DEF_PARAMETRIC_TEMPLATES,
						DESC_PARAMETRIC_TEMPLATES, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_PARAMETRIC_SINGLE_THREADS, DEF_PARAMETRIC_SINGLE_THREADS,
						DESC_PARAMETRIC_SINGLE_THREADS, PreferenceType.String),
				// Settings for thread-modular proofs
				new UltimatePreferenceItem<>(LABEL_THREADMODULAR_LEVEL, DEF_THREADMODULAR_LEVEL,
						DESC_THREADMODULAR_LEVEL, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_SYMMETRY_CLAUSES, DEF_SYMMETRY_CLAUSES, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_LOCATIONS, DEF_EXPLICIT_LOCATIONS, DESC_EXPLICIT_LOCATIONS,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LIPTON_REDUCTION, DEF_LIPTON_REDUCTION, DESC_LIPTON_REDUCTION,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SKIP_ASSERT_EDGES, DEF_SKIP_ASSERT_EDGES, DESC_SKIP_ASSERT_EDGES,
						PreferenceType.Boolean),
				getSleepSetSettings() };
	}

	private static UltimatePreferenceItemContainer getSleepSetSettings() {
		final var container = new UltimatePreferenceItemContainer("Sleep Set Reduction");
		container.addItem(new UltimatePreferenceItem<>(LABEL_SLEEP_SET_REDUCTION, DEF_SLEEP_SET_REDUCTION,
				DESC_SLEEP_SET_REDUCTION, PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_BREAK_PREFORDER_SYMMETRY, DEF_BREAK_PREFORDER_SYMMETRY,
				DESC_BREAK_PREFORDER_SYMMETRY, PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_EXPLICIT_SLEEP, DEF_EXPLICIT_SLEEP, DESC_EXPLICIT_SLEEP,
				PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_PREFERENCE_ORDER, DEF_PREFERENCE_ORDER,
				PreferenceType.Combo, PreferenceOrder.values()));
		container.addItem(new UltimatePreferenceItem<>(LABEL_CONDITIONAL_INDEPENDENCE, DEF_CONDITIONAL_INDEPENDENCE,
				PreferenceType.Combo, ConditionalIndependence.values()));
		container.addItem(
				new UltimatePreferenceItem<>(LABEL_SEMICOMMUTATIVITY, DEF_SEMICOMMUTATIVITY, PreferenceType.Boolean));
		return container;
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}
}
