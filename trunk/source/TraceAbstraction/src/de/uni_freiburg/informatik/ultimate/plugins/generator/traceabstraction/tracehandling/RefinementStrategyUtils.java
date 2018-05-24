/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Objects;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Provides static auxiliary methods for {@link RefinementStrategy}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class RefinementStrategyUtils {

	public static final String COMMAND_Z3_NO_TIMEOUT = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	public static final String COMMAND_Z3_TIMEOUT = COMMAND_Z3_NO_TIMEOUT + " -t:12000";
	public static final String COMMAND_CVC4_NO_TIMEOUT = getCvc4NoTimeout();
	public static final String COMMAND_CVC4_TIMEOUT = COMMAND_CVC4_NO_TIMEOUT + " --tlimit-per=12000";

	// 20161214 Matthias: MathSAT does not support timeouts
	public static final String COMMAND_MATHSAT = "mathsat -unsat_core_generation=3";
	public static final long TIMEOUT_SMTINTERPOL = 12_000L;
	public static final long TIMEOUT_NONE_SMTINTERPOL = 0L;
	public static final String LOGIC_Z3 = "ALL";
	public static final String LOGIC_CVC4_DEFAULT = "AUFLIRA";
	public static final String LOGIC_CVC4_BITVECTORS = "AUFBV";
	public static final String LOGIC_MATHSAT = "ALL";

	private RefinementStrategyUtils() {
		// do not instantiate utility classes
	}

	/**
	 * On Windows we do not have the "golden copy" of cvc4 anymore. Newer versions require a different commandline, so
	 * we switch here based on the OS in use.
	 *
	 * @return the command to start cvc4
	 */
	private static final String getCvc4NoTimeout() {
		if (CoreUtil.OS_IS_WINDOWS) {
			return "cvc4 --tear-down-incremental=1 --print-success --lang smt --rewrite-divk";
		}
		return "cvc4 --tear-down-incremental --print-success --lang smt --rewrite-divk";
	}

	public static <LETTER extends IIcfgTransition<?>> IInterpolantGenerator<LETTER> constructInterpolantGenerator(
			final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final TAPreferences taPrefsForInterpolantConsolidation,
			final ITraceCheck traceCheck, final PredicateFactory predicateFactory,
			final PredicateUnifier predicateUnifier, final IRun<LETTER, IPredicate, ?> counterexample,
			final RefinementEngineStatisticsGenerator statistics) {
		final ITraceCheck localTraceCheck = Objects.requireNonNull(traceCheck,
				"cannot construct interpolant generator if no trace checker is present");
		if (localTraceCheck instanceof InterpolatingTraceCheck) {
			final InterpolatingTraceCheck<LETTER> interpolatingTraceCheck =
					(InterpolatingTraceCheck<LETTER>) localTraceCheck;

			if (prefs.getUseInterpolantConsolidation()) {
				try {
					final CfgSmtToolkit cfgSmtToolkit = prefs.getCfgSmtToolkit();
					final InterpolantConsolidation<LETTER> interpConsoli =
							new InterpolantConsolidation<>(predicateUnifier.getTruePredicate(),
									predicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
									NestedWord.nestedWord(counterexample.getWord()), cfgSmtToolkit,
									cfgSmtToolkit.getModifiableGlobalsTable(), services, logger, predicateFactory,
									predicateUnifier, interpolatingTraceCheck, taPrefsForInterpolantConsolidation);
					statistics.addInterpolantConsolidationStatistics(
							interpConsoli.getInterpolantConsolidationBenchmarks());
					return interpConsoli;
				} catch (final AutomataOperationCanceledException e) {
					throw new AssertionError("react on timeout, not yet implemented");
				}
			}
			return interpolatingTraceCheck;
		}
		throw new AssertionError("Currently only interpolating trace checkers are supported.");
	}

	/**
	 *
	 * @return true iff classified term does not contain {@link SmtUtils#FLOATINGPOINT_SORT}.
	 */
	public static boolean hasNoFloats(final TermClassifier tc) {
		return !tc.getOccuringSortNames().contains(SmtSortUtils.FLOATINGPOINT_SORT);
	}

	/**
	 *
	 * @return true iff classified term does not contain {@link SmtUtils#FP_TO_IEEE_BV_EXTENSION} and does not contain
	 *         quantifiers.
	 */
	public static boolean hasNoQuantifiersNoBitvectorExtensions(final TermClassifier tc) {
		return !tc.getOccuringFunctionNames().contains(SmtUtils.FP_TO_IEEE_BV_EXTENSION)
				&& tc.getOccuringQuantifiers().isEmpty();
	}

}
