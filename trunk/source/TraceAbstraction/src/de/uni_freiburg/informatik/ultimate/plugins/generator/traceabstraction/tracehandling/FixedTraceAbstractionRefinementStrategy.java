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

import java.util.NoSuchElementException;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * {@link IRefinementStrategy} that provides only one element, namely the one selected in the Ultimate preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class FixedTraceAbstractionRefinementStrategy
		implements IRefinementStrategy<NestedWordAutomaton<CodeBlock, IPredicate>> {
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
	private final IAutomaton<CodeBlock, IPredicate> mAbstraction;
	private final IInterpolantAutomatonEvaluator mEvaluator;
	private final PredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	
	private final TraceCheckerConstructor mFunConstructFromPrefs;
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private NestedWordAutomaton<CodeBlock, IPredicate> mInterpolantAutomaton;
	private AutomataOperationCanceledException mInterpolantAutomatonGenerationException;
	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;
	
	/**
	 * @param prefs
	 *            Preferences.
	 *            pending contexts
	 * @param cfgSmtToolkit
	 *            CFG-SMT toolkit
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 */
	public FixedTraceAbstractionRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences prefs,
			final ManagedScript managedScript, final IUltimateServiceProvider services,
			final PredicateUnifier predicateUnifier, final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantAutomatonEvaluator evaluator,
			final TAPreferences taPrefsForInterpolantConsolidation) {
		mLogger = logger;
		mPrefs = prefs;
		mServices = services;
		mAbstraction = abstraction;
		mEvaluator = evaluator;
		mPredicateUnifier = predicateUnifier;
		mCounterexample = counterexample;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		mFunConstructFromPrefs = new TraceCheckerConstructor(prefs, managedScript, services, predicateUnifier,
				counterexample, mPrefs.getInterpolationTechnique());
	}
	
	@Override
	public boolean hasNext() {
		return false;
	}
	
	@Override
	public void next() {
		throw new NoSuchElementException("This strategy has only one element.");
	}
	
	@Override
	public TraceChecker getTraceChecker() {
		if (mTraceChecker == null) {
			mTraceChecker = mFunConstructFromPrefs.get();
			constructInterpolantAutomaton();
		}
		return mTraceChecker;
	}
	
	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		if (mInterpolantGenerator == null) {
			throw new UnsupportedOperationException("There is no infeasibility proof available.");
		}
		return mInterpolantGenerator;
	}
	
	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getInfeasibilityProof() {
		if (mInterpolantAutomaton == null) {
			throw new UnsupportedOperationException("There is no interpolant automaton.");
		}
		if (mInterpolantAutomatonGenerationException != null) {
			throw new ToolchainCanceledException(mInterpolantAutomatonGenerationException.getClassOfThrower());
		}
		return mInterpolantAutomaton;
	}
	
	private void constructInterpolantAutomaton() throws AssertionError {
		// mTraceCheckerBenchmark.aggregateBenchmarkData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		mInterpolantGenerator = constructInterpolantGenerator();
		try {
			mInterpolantAutomaton = generateInterpolantAutomaton();
		} catch (final AutomataOperationCanceledException e) {
			mInterpolantAutomatonGenerationException = e;
		}
	}
	
	private IInterpolantGenerator constructInterpolantGenerator()
			throws AssertionError {
		final IInterpolantGenerator interpolantGenerator;
		final InterpolatingTraceChecker interpolatingTraceChecker =
				(getTraceChecker() instanceof InterpolatingTraceChecker)
						? (InterpolatingTraceChecker) getTraceChecker()
						: null;
		if (interpolatingTraceChecker != null) {
			if (mPrefs.getUseInterpolantConsolidation()) {
				try {
					interpolantGenerator = consolidateInterpolants(interpolatingTraceChecker);
				} catch (final AutomataOperationCanceledException e) {
					// Timeout
					throw new AssertionError("react on timeout, not yet implemented");
				}
			} else {
				interpolantGenerator = interpolatingTraceChecker;
			}
		} else {
			// TODO insert code here to support generating interpolants from a different source
			throw new AssertionError("Currently only interpolating trace checkers are supported.");
		}
		return interpolantGenerator;
	}
	
	private IInterpolantGenerator consolidateInterpolants(final InterpolatingTraceChecker interpolatingTraceChecker)
			throws AutomataOperationCanceledException {
		final IInterpolantGenerator interpolantGenerator;
		final CfgSmtToolkit cfgSmtToolkit = mPrefs.getCfgSmtToolkit();
		final InterpolantConsolidation interpConsoli = new InterpolantConsolidation(
				mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
				new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()), cfgSmtToolkit,
				cfgSmtToolkit.getModifiableGlobalsTable(), mServices, mLogger, mPredicateUnifier,
				interpolatingTraceChecker, mTaPrefsForInterpolantConsolidation);
		// Add benchmark data of interpolant consolidation
		mPrefs.getCegarLoopBenchmark()
				.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
		interpolantGenerator = interpConsoli;
		return interpolantGenerator;
	}
	
	private NestedWordAutomaton<CodeBlock, IPredicate> generateInterpolantAutomaton()
			throws AutomataOperationCanceledException {
		final IInterpolantAutomatonBuilder<CodeBlock, IPredicate> builder =
				mPrefs.getInterpolantAutomatonBuilderFactory().createBuilder(mAbstraction, mInterpolantGenerator,
						mCounterexample);
		final NestedWordAutomaton<CodeBlock, IPredicate> automaton = builder.getResult();
		
		if (mEvaluator.accept(automaton)) {
			return automaton;
		}
		// TODO add code to construct the next automaton
		mLogger.debug("The interpolant automaton is not considered good, but at the moment we still use it.");
		return automaton;
	}
}
