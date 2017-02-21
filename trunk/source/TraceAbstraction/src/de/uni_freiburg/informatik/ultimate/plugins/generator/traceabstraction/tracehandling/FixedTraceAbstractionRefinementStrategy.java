/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * {@link IRefinementStrategy} that provides only one element, namely the one selected in the Ultimate preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class FixedTraceAbstractionRefinementStrategy<LETTER extends IIcfgTransition<?>>
		implements IRefinementStrategy<LETTER> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final PredicateUnifier mPredicateUnifier;

	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;

	private final TraceCheckerConstructor<LETTER> mFunConstructFromPrefs;
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<LETTER, IPredicate> mInterpolantAutomatonBuilder;
	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	/**
	 * @param prefs
	 *            Preferences. pending contexts
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param logger
	 *            logger
	 * @param abstraction
	 *            abstraction
	 * @param taPrefsForInterpolantConsolidation
	 *            temporary argument, should be removed
	 * @param iteration
	 *            current CEGAR loop iteration
	 * @param cegarLoopBenchmarks
	 *            benchmark
	 */
	public FixedTraceAbstractionRefinementStrategy(final ILogger logger,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final PredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mCounterexample = counterexample;
		mAbstraction = abstraction;
		mPredicateUnifier = predicateUnifier;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		mCegarLoopBenchmark = cegarLoopBenchmarks;
		mFunConstructFromPrefs = new TraceCheckerConstructor<>(prefs, managedScript, services, predicateUnifier,
				counterexample, mPrefs.getInterpolationTechnique(), iteration, cegarLoopBenchmarks);
	}

	@Override
	public boolean hasNextTraceChecker() {
		return false;
	}

	@Override
	public void nextTraceChecker() {
		throw new NoSuchElementException("This strategy has only one element.");
	}

	@Override
	public TraceChecker getTraceChecker() {
		if (mTraceChecker == null) {
			mTraceChecker = mFunConstructFromPrefs.get();
		}
		return mTraceChecker;
	}

	@Override
	public boolean hasNextInterpolantGenerator(final List<InterpolantsPreconditionPostcondition> perfectIpps,
			final List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		return false;
	}

	@Override
	public void nextInterpolantGenerator() {
		throw new NoSuchElementException("This strategy has only one element.");
	}

	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = RefinementStrategyUtils.constructInterpolantGenerator(mServices, mLogger, mPrefs,
					mTaPrefsForInterpolantConsolidation, getTraceChecker(), mPredicateUnifier, mCounterexample,
					mCegarLoopBenchmark);
		}
		return mInterpolantGenerator;
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<InterpolantsPreconditionPostcondition> perfectIpps,
			final List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		// use all interpolant sequences
		final List<InterpolantsPreconditionPostcondition> allIpps =
				IRefinementStrategy.wrapTwoListsInOne(perfectIpps, imperfectIpps);

		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder = constructInterpolantAutomatonBuilder(getInterpolantGenerator(), allIpps);
		}
		return mInterpolantAutomatonBuilder;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> constructInterpolantAutomatonBuilder(
			final IInterpolantGenerator interpolantGenerator, final List<InterpolantsPreconditionPostcondition> ipps) {
		final IInterpolantGenerator localInterpolantGenerator = Objects.requireNonNull(interpolantGenerator,
				"cannot construct interpolant automaton if no interpolant generator is present");
		try {
			if (ipps.isEmpty()) {
				throw new IllegalArgumentException("Need at least one sequence of interpolants.");
			}
			return mPrefs.getInterpolantAutomatonBuilderFactory().createBuilder(mAbstraction, localInterpolantGenerator,
					mCounterexample, ipps);
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(this.getClass(), "creating interpolant automaton"));
		}
	}

	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mPrefs.getExceptionBlacklist();
	}
}
