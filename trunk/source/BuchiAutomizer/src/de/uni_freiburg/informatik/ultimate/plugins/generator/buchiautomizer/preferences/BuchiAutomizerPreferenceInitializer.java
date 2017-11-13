/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class BuchiAutomizerPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum BuchiInterpolantAutomaton {
		/**
		 * Only the lasso, considered as an automaton.
		 */
		LassoAutomaton, 
		/**
		 * Use predicate obtained for the lasso. Add as many edge as possible.
		 * Resulting automaton is in general not semideterministic and
		 * the complementation is very costly.
		 */
		EagerNondeterminism, 
		/**
		 * Automaton that is mainly deterministic but can have some
		 * nondeterministic transitions.
		 * (Does not guarantee that automaton is semideterministic
		 */
		ScroogeNondeterminism, 
		/**
		 * Automaton that is deterministic. 
		 * As we know from Büchi, there are
		 * omega-regular languages that are not accepted by any deterministic
		 * Büchi automaton.
		 * Practical experience shows that we sometimes need such languages
		 * in the termination analysis. Hence using only deterministic
		 * automata is not sufficient. 
		 */
		Deterministic, 
		/**
		 * Try different automata iteratively. Start with less nondeterministic
		 * automata, increase amount of nondeterminism until an appropriate
		 * automaton was found.
		 */
		Staged, 
	}

	public enum BuchiComplementationConstruction {
		Ncsb, Elastic, HeiMat2, TightRO, TightBasic, TightHighEven
	}
	
	public enum NcsbImplementation {
		ORIGINAL, INTSET, INTSET_GBA, INTSET_GBA_LAZY, INTSET_GBA_ANTICHAIN, INTSET_GBA_LAZY_ANTICHAIN, INTSET_LAZY, INTSET_LAZY2, INTSET_LAZY3
	}


	public static final String LABEL_IGNORE_DOWN_STATES = "Ignore down states";
	public static final String LABEL_DETERMINIZATION_ON_DEMAND = "Determinization on demand";
	public static final String LABEL_BIA_CONSTRUCTION_STRATEGY = "Buchi interpolant automaton construction strategy";
	public static final BuchiInterpolantAutomatonConstructionStrategy DEF_BIA_CONSTRUCTION_STRATEGY = 
			BuchiInterpolantAutomatonConstructionStrategy.RHODODENDRON;
	public static final String LABEL_BUCHI_INTERPOLANT_AUTOMATON = "Buchi interpolant automaton";
	public static final String LABEL_BUCHI_COMPLEMENTATION_CONSTRUCTION = "Buchi complementation construction";
	public static final String LABEL_BOUNCER_STEM = "Bouncer stem";
	public static final String LABEL_BOUNCER_LOOP = "Bouncer loop";
	public static final String LABEL_SCROOGE_NONDETERMINISM_STEM = "ScroogeNondeterminism stem";
	public static final String LABEL_SCROOGE_NONDETERMINISM_LOOP = "ScroogeNondeterminism loop";
	public static final String LABEL_CANNIBALIZE_LOOP = "Cannibalize loop";
	public static final String LABEL_LOOP_UNWINDINGS = "Max number of loop unwindings";
	public static final String LABEL_USE_EXTERNAL_SOLVER_RANK = "Use external solver (rank synthesis)";
	public static final String LABEL_EXTERNAL_SOLVER_COMMAND_RANK = "Command for external solver (rank synthesis)";
	private static final String DEF_EXTERNAL_SOLVER_COMMAND_RANK =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String LABEL_ANALYSIS_TYPE_RANK = "Rank analysis";
	public static final String LABEL_USE_EXTERNAL_SOLVER_GNTA = "Use external solver (GNTA synthesis)";
	public static final String LABEL_EXTERNAL_SOLVER_COMMAND_GNTA = "Command for external solver (GNTA synthesis)";
	private static final String DEF_EXTERNAL_SOLVER_COMMAND_GNTA =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String LABEL_ANALYSIS_TYPE_GNTA = "GNTA analysis";
	public static final String LABEL_GNTA_DIRECTIONS = "Number of GNTA directions";
	private static final int DEF_GNTA_DIRECTIONS = 3;
	public static final String LABEL_TEMPLATE_BENCHMARK_MODE = "Template benchmark mode";
	public static final String LABEL_DUMP_SCRIPT_TO_FILE = "Dump SMT script to file";
	public static final String LABEL_DUMP_SCRIPT_PATH = "To the following directory";
	private static final String DEF_DUMP_SCRIPT_PATH = "";
	public static final String LABEL_CONSTRUCT_TERMCOMP_PROOF = "Construct termination proof for TermComp";
	public static final String LABEL_SIMPLIFY = "Try to simplify termination arguments";
	public static final String LABEL_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT = 
			"Automata minimization after feasibility-based refinement";
	public static final String LABEL_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT = 
			"Automata minimization after rank-based refinement";
	private static final Minimization DEF_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT = Minimization.MINIMIZE_SEVPA;
	private static final Minimization DEF_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT = Minimization.MINIMIZE_SEVPA;
	/**
	 * If true we check if the loop is terminating even if the stem or the concatenation of stem and loop are already
	 * infeasible. This allows us to use refineFinite and refineBuchi in the same iteration.
	 */
	public static final String LABEL_TRY_TWOFOLD_REFINEMENT = "Try twofold refinement";

	public static final String LABEL_USE_OLD_MAP_ELIMINATION = "Use old map elimination";
	private static final boolean DEF_USE_OLD_MAP_ELIMINATION = true;

	public static final String LABEL_MAP_ELIMINATION_ADD_INEQUALITIES =
			"Add inequalities as additional conjuncts to the transformula";
	private static final boolean DEF_MAP_ELIMINATION_ADD_INEQUALITIES = false;
	public static final String LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT =
			"Use only trivial implications for index assignments";
	private static final boolean DEF_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT = true;
	public static final String LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE =
			"Use only trivial implications for array writes";
	private static final boolean DEF_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE = false;
	public static final String LABEL_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS =
			"Add implications only for indices occuring in the current formula";
	private static final boolean DEF_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS = true;
	public static final String LABEL_NCSB_IMPLEMENTATION = "NCSB implementation";
	private static final NcsbImplementation DEF_NCSB_IMPLEMENTATION = NcsbImplementation.ORIGINAL;

	public BuchiAutomizerPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Buchi Automizer (Termination Analysis)");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_IGNORE_DOWN_STATES, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DETERMINIZATION_ON_DEMAND, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BUCHI_COMPLEMENTATION_CONSTRUCTION,
						BuchiComplementationConstruction.Ncsb, PreferenceType.Combo, BuchiComplementationConstruction.values()),
				new UltimatePreferenceItem<>(LABEL_BIA_CONSTRUCTION_STRATEGY, DEF_BIA_CONSTRUCTION_STRATEGY,
						PreferenceType.Combo, BuchiInterpolantAutomatonConstructionStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_BUCHI_INTERPOLANT_AUTOMATON, BuchiInterpolantAutomaton.Staged,
						PreferenceType.Combo, BuchiInterpolantAutomaton.values()),
				new UltimatePreferenceItem<>(LABEL_BOUNCER_STEM, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BOUNCER_LOOP, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SCROOGE_NONDETERMINISM_STEM, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SCROOGE_NONDETERMINISM_LOOP, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CANNIBALIZE_LOOP, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LOOP_UNWINDINGS, 2, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_000_000)),
				new UltimatePreferenceItem<>(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
						InterpolationTechnique.ForwardPredicates, PreferenceType.Combo,
						TraceAbstractionPreferenceInitializer.InterpolationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_USE_EXTERNAL_SOLVER_RANK, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EXTERNAL_SOLVER_COMMAND_RANK, DEF_EXTERNAL_SOLVER_COMMAND_RANK,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_ANALYSIS_TYPE_RANK, AnalysisType.NONLINEAR, PreferenceType.Combo,
						AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_USE_EXTERNAL_SOLVER_GNTA, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EXTERNAL_SOLVER_COMMAND_GNTA, DEF_EXTERNAL_SOLVER_COMMAND_GNTA,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_ANALYSIS_TYPE_GNTA, AnalysisType.NONLINEAR, PreferenceType.Combo,
						AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_GNTA_DIRECTIONS, DEF_GNTA_DIRECTIONS, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_TEMPLATE_BENCHMARK_MODE, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_SCRIPT_TO_FILE, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_SCRIPT_PATH, DEF_DUMP_SCRIPT_PATH, PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_CONSTRUCT_TERMCOMP_PROOF, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLIFY, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_TRY_TWOFOLD_REFINEMENT, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT, 
						DEF_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT,
						PreferenceType.Combo, Minimization.values()),
				new UltimatePreferenceItem<>(LABEL_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT, 
						DEF_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT,
						PreferenceType.Combo, Minimization.values()),
				new UltimatePreferenceItem<>(LABEL_USE_OLD_MAP_ELIMINATION, DEF_USE_OLD_MAP_ELIMINATION,
						"Use either Matthias' (old) or Frank's (new) implementation of a map elimination algorithm",
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MAP_ELIMINATION_ADD_INEQUALITIES,
						DEF_MAP_ELIMINATION_ADD_INEQUALITIES, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT,
						DEF_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_INDEX_ASSIGNMENT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE,
						DEF_MAP_ELIMINATION_ONLY_TRIVIAL_IMPLICATIONS_ARRAY_WRITE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS,
						DEF_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_NCSB_IMPLEMENTATION,
						DEF_NCSB_IMPLEMENTATION, PreferenceType.Combo, NcsbImplementation.values()) 
				};
	}
}
