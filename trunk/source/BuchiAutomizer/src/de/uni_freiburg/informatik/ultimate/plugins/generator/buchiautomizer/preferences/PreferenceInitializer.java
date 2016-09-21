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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Buchi Automizer (Termination Analysis)");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_IgnoreDownStates, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DeterminizationOnDemand, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BuchiComplementationConstruction, BComplementationConstruction.Ncsb,
						PreferenceType.Combo, BComplementationConstruction.values()),
				new UltimatePreferenceItem<>(LABEL_BuchiInterpolantAutomaton, BInterpolantAutomaton.Staged,
						PreferenceType.Combo, BInterpolantAutomaton.values()),
				new UltimatePreferenceItem<>(LABEL_BouncerStem, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BouncerLoop, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ScroogeNondeterminismStem, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ScroogeNondeterminismLoop, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CannibalizeLoop, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LoopUnwindings, 2, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 1000000)),
				new UltimatePreferenceItem<>(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
						InterpolationTechnique.ForwardPredicates, PreferenceType.Combo,
						TraceAbstractionPreferenceInitializer.InterpolationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_ExtSolverRank, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ExtSolverCommandRank, DEF_ExtSolverCommandRank,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_AnalysisTypeRank, AnalysisType.Nonlinear, PreferenceType.Combo,
						AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_ExtSolverGNTA, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ExtSolverCommandGNTA, DEF_ExtSolverCommandGNTA,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_AnalysisTypeGNTA, AnalysisType.Nonlinear, PreferenceType.Combo,
						AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_GntaDirections, DEF_GntaDirections, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_TemplateBenchmarkMode, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DumpToFile, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DumpPath, DEF_DumpPath, PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_TermcompProof, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_Simplify, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_TryTwofoldRefinement, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_AutomataMinimization, DEF_AutomataMinimization, PreferenceType.Combo,
						AutomataMinimization.values()),
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
						DEF_MAP_ELIMINATION_ONLY_INDICES_IN_FORMULAS, PreferenceType.Boolean), };
	}

	public static final String LABEL_IgnoreDownStates = "Ignore down states";
	public static final String LABEL_DeterminizationOnDemand = "Determinization on demand";
	public static final String LABEL_BuchiInterpolantAutomaton = "Buchi interpolant automaton";
	public static final String LABEL_BuchiComplementationConstruction = "Buchi complementation construction";
	public static final String LABEL_BouncerStem = "Bouncer stem";
	public static final String LABEL_BouncerLoop = "Bouncer loop";
	public static final String LABEL_ScroogeNondeterminismStem = "ScroogeNondeterminism stem";
	public static final String LABEL_ScroogeNondeterminismLoop = "ScroogeNondeterminism loop";
	public static final String LABEL_CannibalizeLoop = "Cannibalize loop";
	public static final String LABEL_LoopUnwindings = "Max number of loop unwindings";
	public static final String LABEL_ExtSolverRank = "Use external solver (rank synthesis)";
	public static final String LABEL_ExtSolverCommandRank = "Command for external solver (rank synthesis)";
	private static final String DEF_ExtSolverCommandRank = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String LABEL_AnalysisTypeRank = "Rank analysis";
	public static final String LABEL_ExtSolverGNTA = "Use external solver (GNTA synthesis)";
	public static final String LABEL_ExtSolverCommandGNTA = "Command for external solver (GNTA synthesis)";
	private final String DEF_ExtSolverCommandGNTA = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String LABEL_AnalysisTypeGNTA = "GNTA analysis";
	public static final String LABEL_GntaDirections = "Number of GNTA directions";
	private static final int DEF_GntaDirections = 3;
	public static final String LABEL_TemplateBenchmarkMode = "Template benchmark mode";
	public static final String LABEL_DumpToFile = "Dump SMT script to file";
	public static final String LABEL_DumpPath = "To the following directory";
	private static final String DEF_DumpPath = "";
	public static final String LABEL_TermcompProof = "Construct termination proof for TermComp";
	public static final String LABEL_Simplify = "Try to simplify termination arguments";
	public static final String LABEL_AutomataMinimization = "Automata minimization";
	private static final AutomataMinimization DEF_AutomataMinimization = AutomataMinimization.None;
	/**
	 * If true we check if the loop is terminating even if the stem or the concatenation of stem and loop are already
	 * infeasible. This allows us to use refineFinite and refineBuchi in the same iteration.
	 */
	public static final String LABEL_TryTwofoldRefinement = "Try twofold refinement";

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

	public enum BInterpolantAutomaton {
		LassoAutomaton, EagerNondeterminism, ScroogeNondeterminism, Deterministic, Staged, TwoStage
	}

	public enum BComplementationConstruction {
		Ncsb, Elastic, HeiMat2, TightRO, TightBasic, TightHighEven
	}

	public enum AutomataMinimization {
		None, MinimizeSevpa, ShrinkNwa, DelayedSimulation, FairSimulation_WithSCC, FairSimulation_WithoutSCC, FairDirectSimulation, MinimizeNwaMaxSat2, MinimizeNwaMaxSat, RaqDirectSimulation, RaqDelayedSimulation, MultiDefault, MultiSimulation
	}
}
