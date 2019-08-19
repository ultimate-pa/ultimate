/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

public class CodeCheckPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum EdgeCheckOptimization {
		NONE, PUSHPOP, SDEC, PUSHPOP_SDEC
	}

	public enum PredicateUnification {
		PER_ITERATION, PER_VERIFICATION, NONE
	}

	public enum Checker {
		ULTIMATE, IMPULSE
	}

	public enum RedirectionStrategy {
		No_Strategy, FIRST, RANDOM, RANDOmSTRONGEST
	}

	public static final String LABEL_CHECKER = "the checking algorithm to use";

	public static final String LABEL_MEMOIZENORMALEDGECHECKS = "memoize already made edge checks for non-return edges";
	public static final String LABEL_MEMOIZERETURNEDGECHECKS = "memoize already made edge checks for return edges";

	public static final String LABEL_SOLVERANDINTERPOLATOR = "Interpolating solver";
	public static final String LABEL_INTERPOLATIONMODE = "interpolation mode";
	public static final String LABEL_INTERPOLANTCONSOLIDATION =
			"use interpolant consolidation (only useful for interpolationmode fp+bp)";
	public static final String LABEL_PREDICATEUNIFICATION = "Predicate Unification Mode";
	public static final String LABEL_EDGECHECKOPTIMIZATION = "EdgeCheck Optimization Mode";

	public static final String LABEL_GRAPHWRITERPATH = "write dot graph files here (empty for don't write)";

	public static final String LABEL_TIMEOUT = "Timeout in seconds";

	public static final String LABEL_ITERATIONS = "Limit maxmium number of iterations. (-1 for no limitations)";

	public static final String LABEL_REDIRECTION = "The redirection strategy for Impulse";

	public static final String LABEL_DEF_RED = "Default Redirection";

	public static final String LABEL_RmFALSE = "Remove False Nodes Manually";

	public static final String LABEL_CHK_SAT = "Check edges satisfiability";

	public static final String LABEL_USESEPARATETRACECHECKSOLVER = "Use separate solver for tracechecks";
	public static final String LABEL_CHOOSESEPARATETRACECHECKSOLVER =
			"Choose which separate solver to use for tracechecks";
	public static final String LABEL_SEPARATETRACECHECKSOLVERCOMMAND = "Command for calling external solver";
	public static final String LABEL_SEPARATETRACECHECKSOLVERTHEORY = "Theory for external solver";
	public static final String LABEL_USEFALLBACKFORSEPARATETRACECHECKSOLVER =
			"Use standard solver (from RCFGBuilder) with FP interpolation as fallback";

	public static final String LABEL_UNSAT_CORES = "Use unsat cores in FP/BP interpolation";
	public static final String LABEL_LIVE_VARIABLES = "Use live variables in FP/BP interpolation";

	public static final String LABEL_USE_ABSTRACT_INTERPRETATION = "Use predicates from abstract interpretation";

	public static final String LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER =
			TraceAbstractionPreferenceInitializer.LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER;

	public static final Checker DEF_CHECKER = Checker.ULTIMATE;

	public static final boolean DEF_MEMOIZENORMALEDGECHECKS = true;
	public static final boolean DEF_MEMOIZERETURNEDGECHECKS = true;

	public static final InterpolationTechnique DEF_INTERPOLATIONMODE = InterpolationTechnique.Craig_TreeInterpolation;
	public static final boolean DEF_INTERPOLANTCONSOLIDATION = false;
	public static final PredicateUnification DEF_PREDICATEUNIFICATION = PredicateUnification.PER_ITERATION;
	public static final EdgeCheckOptimization DEF_EDGECHECKOPTIMIZATION = EdgeCheckOptimization.NONE;

	public static final String DEF_GRAPHWRITERPATH = "";

	public static final int DEF_TIMEOUT = 100000;

	public static final int DEF_ITERATIONS = -1;

	public static final RedirectionStrategy DEF_REDIRECTION = RedirectionStrategy.RANDOmSTRONGEST;

	public static final boolean DEF_DEF_RED = false;

	public static final boolean DEF_RmFALSE = false;

	public static final boolean DEF_CHK_SAT = false;

	public static final boolean DEF_USESEPARATETRACECHECKSOLVER = true;
	public static final SolverMode DEF_CHOOSESEPARATETRACECHECKSOLVER = SolverMode.Internal_SMTInterpol;
	public static final String DEF_SEPARATETRACECHECKSOLVERCOMMAND = "";
	public static final String DEF_SEPARATETRACECHECKSOLVERTHEORY = "QF_AUFLIA";
	public static final boolean DEF_USEFALLBACKFORSEPARATETRACECHECKSOLVER = true;

	public static final boolean DEF_USE_ABSTRACT_INTERPRETATION = false;

	public CodeCheckPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "CodeCheck");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				/*
				 * settings concerning the kojak/impulse algorithm
				 */
				new UltimatePreferenceItem<>(LABEL_CHECKER, DEF_CHECKER, PreferenceType.Combo, Checker.values()),
				new UltimatePreferenceItem<>(LABEL_MEMOIZENORMALEDGECHECKS, DEF_MEMOIZENORMALEDGECHECKS,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MEMOIZERETURNEDGECHECKS, DEF_MEMOIZERETURNEDGECHECKS,
						PreferenceType.Boolean),
				/*
				 * settings concerning the interpolation and predicate handling in general
				 */
				new UltimatePreferenceItem<>(LABEL_INTERPOLATIONMODE, DEF_INTERPOLATIONMODE, PreferenceType.Combo,
						InterpolationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANTCONSOLIDATION, DEF_INTERPOLANTCONSOLIDATION,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_PREDICATEUNIFICATION, DEF_PREDICATEUNIFICATION, PreferenceType.Combo,
						PredicateUnification.values()),
				new UltimatePreferenceItem<>(LABEL_EDGECHECKOPTIMIZATION, DEF_EDGECHECKOPTIMIZATION,
						PreferenceType.Combo, EdgeCheckOptimization.values()),
				new UltimatePreferenceItem<>(LABEL_EDGECHECKOPTIMIZATION, DEF_EDGECHECKOPTIMIZATION,
						PreferenceType.Combo, EdgeCheckOptimization.values()),
				new UltimatePreferenceItem<>(
						TraceAbstractionPreferenceInitializer.LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						DEF_EDGECHECKOPTIMIZATION, PreferenceType.Combo, EdgeCheckOptimization.values()),
				new UltimatePreferenceItem<>(LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						TraceAbstractionPreferenceInitializer.DEF_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						TraceAbstractionPreferenceInitializer.DESC_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						PreferenceType.Boolean),

				/*
				 * settings concerning a separate solver for trace checks and interpolation
				 */
				new UltimatePreferenceItem<>(LABEL_USESEPARATETRACECHECKSOLVER, DEF_USESEPARATETRACECHECKSOLVER,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHOOSESEPARATETRACECHECKSOLVER, DEF_CHOOSESEPARATETRACECHECKSOLVER,
						PreferenceType.Combo, SolverMode.values()),
				new UltimatePreferenceItem<>(LABEL_SEPARATETRACECHECKSOLVERCOMMAND, DEF_SEPARATETRACECHECKSOLVERCOMMAND,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_SEPARATETRACECHECKSOLVERTHEORY, DEF_SEPARATETRACECHECKSOLVERTHEORY,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_USEFALLBACKFORSEPARATETRACECHECKSOLVER,
						DEF_USEFALLBACKFORSEPARATETRACECHECKSOLVER, PreferenceType.Boolean),
				/*
				 * settings concerning betim interpolation
				 */
				new UltimatePreferenceItem<>(LABEL_UNSAT_CORES, UnsatCores.CONJUNCT_LEVEL, PreferenceType.Combo,
						UnsatCores.values()),
				new UltimatePreferenceItem<>(LABEL_LIVE_VARIABLES, true, PreferenceType.Boolean),
				/*
				 * settings used mostly for debugging
				 */
				new UltimatePreferenceItem<>(LABEL_GRAPHWRITERPATH, DEF_GRAPHWRITERPATH, PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_TIMEOUT, DEF_TIMEOUT, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 100000)),
				new UltimatePreferenceItem<>(LABEL_ITERATIONS, DEF_ITERATIONS, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(-1, 100000)),
				/*
				 * settings concerning only impulse
				 */
				new UltimatePreferenceItem<>(LABEL_REDIRECTION, DEF_REDIRECTION, PreferenceType.Combo,
						RedirectionStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_DEF_RED, DEF_DEF_RED, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHK_SAT, DEF_CHK_SAT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_RmFALSE, DEF_RmFALSE, PreferenceType.Boolean),

				/*
				 * Abstract interpretation settings
				 */
				new UltimatePreferenceItem<>(LABEL_USE_ABSTRACT_INTERPRETATION, DEF_USE_ABSTRACT_INTERPRETATION,
						PreferenceType.Boolean), };
	}

}
