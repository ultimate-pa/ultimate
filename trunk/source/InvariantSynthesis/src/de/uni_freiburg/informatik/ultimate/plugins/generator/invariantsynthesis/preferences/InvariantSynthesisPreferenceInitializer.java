/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE InvariantSynthesis plug-in.
 *
 * The ULTIMATE InvariantSynthesis plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE InvariantSynthesis plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE InvariantSynthesis plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE InvariantSynthesis plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE InvariantSynthesis plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.invariantsynthesis.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.generator.invariantsynthesis.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.KindOfInvariant;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class InvariantSynthesisPreferenceInitializer extends UltimatePreferenceInitializer {
	
	
	public enum IncreasingStrategy {
		Conservative,
		Medium,
		IncrOnlyConjunctsAfterMaxDisjuncts,
		Aggressive,
		ExponentialConjuncts,
		ConjunctsPriorized
	}
	
	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_KIND_INVARIANT = "Kind of invariant";
	
	public static final String LABEL_UNSAT_CORES = "Use unsat cores";
	
	public static final String LABEL_INITIAL_DISJUNCTS = "Initial disjuncts";
	public static final String LABEL_INITIAL_CONJUNCTS = "Initial conjuncts";
	public static final String LABEL_STEP_DISJUNCTS = "Step to increase disjuncts";
	public static final String LABEL_STEP_CONJUNCTS = "Step to increase conjuncts";
	
	public static final String LABEL_NONLINEAR_CONSTRAINTS =
			"Nonlinear constraints";
	
	public static final String LABEL_EXTERNAL_SMT_SOLVER = "Use external solver (z3)";
	public static final String LABEL_SOLVER_TIMEOUT = "Solver timeout (sec)";
	
	public static final String LABEL_LARGE_BLOCK_ENCODING = "Large-Block-Encoding";
	
	public static final String LABEL_INCR_STRATEGY = "Increasing strategy";
	public static final String LABEL_DANGER_INVARIANT_GUESSING = "Guess danger invariant";

	/*
	 * default values for the different preferences
	 */
	public static final KindOfInvariant DEF_KIND_INVARIANT = KindOfInvariant.SAFETY;
	public static final boolean DEF_UNSAT_CORES = true;
	public static final boolean DEF_NONLINEAR_CONSTRAINTS = false;
	public static final boolean DEF_LARGE_BLOCK_ENCODING = true;
	
	public static final int DEF_INITIAL_DISJUNCTS = 1;
	public static final int DEF_INITIAL_CONJUNCTS = 1;
	public static final int DEF_STEP_DISJUNCTS = 1;
	public static final int DEF_STEP_CONJUNCTS = 1;
	
	public static final boolean DEF_EXTERNAL_SMT_SOLVER = true;
	public static final int DEF_SOLVER_TIMEOUT = 15; // in seconds
	
	public static final IncreasingStrategy DEF_INCR_STRATEGY = IncreasingStrategy.Conservative;
	public static final boolean DEF_DANGER_INVARIANT_GUESSING = false;
	
	
	/**
	 * Constructor.
	 */
	public InvariantSynthesisPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Invariant Synthesis");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_KIND_INVARIANT, DEF_KIND_INVARIANT, PreferenceType.Combo, KindOfInvariant.values()),
				new UltimatePreferenceItem<>(LABEL_UNSAT_CORES, DEF_UNSAT_CORES, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_NONLINEAR_CONSTRAINTS, DEF_NONLINEAR_CONSTRAINTS, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LARGE_BLOCK_ENCODING, DEF_LARGE_BLOCK_ENCODING, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INITIAL_DISJUNCTS, DEF_INITIAL_DISJUNCTS, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_STEP_DISJUNCTS, DEF_STEP_DISJUNCTS, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_INITIAL_CONJUNCTS, DEF_INITIAL_CONJUNCTS, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_STEP_CONJUNCTS, DEF_STEP_CONJUNCTS, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_INCR_STRATEGY, DEF_INCR_STRATEGY, PreferenceType.Combo, IncreasingStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_EXTERNAL_SMT_SOLVER, DEF_EXTERNAL_SMT_SOLVER, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SOLVER_TIMEOUT, DEF_SOLVER_TIMEOUT, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_DANGER_INVARIANT_GUESSING, DEF_DANGER_INVARIANT_GUESSING, PreferenceType.Boolean),
		};
	};
}
