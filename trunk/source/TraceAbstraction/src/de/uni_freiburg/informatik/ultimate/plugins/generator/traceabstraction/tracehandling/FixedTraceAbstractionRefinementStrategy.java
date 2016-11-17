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
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckerPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;

/**
 * {@link IRefinementStrategy} that provides only one element, namely the one selected in the Ultimate preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class FixedTraceAbstractionRefinementStrategy implements IRefinementStrategy {
	private final TraceCheckerConstructorFromPreferences mFunConstructTraceChecker;
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	
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
	public FixedTraceAbstractionRefinementStrategy(final TaCheckAndRefinementPreferences prefs,
			final CfgSmtToolkit cfgSmtToolkit, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final PredicateUnifier predicateUnifier,
			final IRun<CodeBlock, IPredicate, ?> counterexample) {
		mFunConstructTraceChecker =
				new TraceCheckerConstructorFromPreferences(prefs, cfgSmtToolkit, managedScript, services,
						predicateUnifier, counterexample);
	}
	
	@Override
	public boolean hasMoreStrategies() {
		return false;
	}
	
	@Override
	public void next() {
		throw new NoSuchElementException("This strategy has only one element.");
	}
	
	@Override
	public TraceChecker getTraceChecker() {
		if (mTraceChecker == null) {
			mTraceChecker = mFunConstructTraceChecker.get();
		}
		return mTraceChecker;
	}
	
	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		return mInterpolantGenerator;
	}
	
	/**
	 * Trace checker constructor on demand.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class TraceCheckerConstructorFromPreferences implements Supplier<TraceChecker> {
		private final TaCheckAndRefinementPreferences mPrefs;
		private final CfgSmtToolkit mCfgSmtToolkit;
		private final ManagedScript mManagedScript;
		private final IUltimateServiceProvider mServices;
		private final PredicateUnifier mPredicateUnifier;
		private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
		
		/**
		 * @param prefs
		 *            Preferences.
		 * @param precondition
		 *            precondition
		 * @param postcondition
		 *            postcondition
		 * @param pendingContexts
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
		public TraceCheckerConstructorFromPreferences(final TaCheckAndRefinementPreferences prefs,
				final CfgSmtToolkit cfgSmtToolkit, final ManagedScript managedScript,
				final IUltimateServiceProvider services, final PredicateUnifier predicateUnifier,
				final IRun<CodeBlock, IPredicate, ?> counterexample) {
			mPrefs = prefs;
			mCfgSmtToolkit = cfgSmtToolkit;
			mManagedScript = managedScript;
			mServices = services;
			mPredicateUnifier = predicateUnifier;
			mCounterexample = counterexample;
		}
		
		@Override
		public TraceChecker get() {
			final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
			final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
			final AssertCodeBlockOrder assertCodeBlocksIncrementally = mPrefs.getAssertCodeBlocksIncrementally();
			final InterpolationTechnique interpolationTechnique = mPrefs.getInterpolationTechnique();
			final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
			final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
			
			final TraceChecker traceChecker;
			switch (interpolationTechnique) {
				case Craig_NestedInterpolation:
				case Craig_TreeInterpolation:
					traceChecker = new InterpolatingTraceCheckerCraig(truePredicate, falsePredicate,
							new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()),
							mCfgSmtToolkit, assertCodeBlocksIncrementally, mServices, true,
							mPredicateUnifier, interpolationTechnique, mManagedScript, true,
							xnfConversionTechnique, simplificationTechnique, mCounterexample.getStateSequence(),
							false);
					break;
				case ForwardPredicates:
				case BackwardPredicates:
				case FPandBP:
					traceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate,
							new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()),
							mCfgSmtToolkit, assertCodeBlocksIncrementally, mPrefs.getUnsatCores(),
							mPrefs.getUseLiveVariables(), mServices, true, mPredicateUnifier,
							interpolationTechnique, mManagedScript, xnfConversionTechnique,
							simplificationTechnique, mCounterexample.getStateSequence());
					
					break;
				case PathInvariants:
					final BoogieIcfgContainer icfgContainer = mPrefs.getIcfgContainer();
					final boolean useNonlinearConstraints = mPrefs.getUseNonlinearConstraints();
					final boolean useVarsFromUnsatCore = mPrefs.getUseVarsFromUnsatCore();
					final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
					final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
					final String baseNameOfDumpedScript =
							"InVarSynth_" + icfgContainer.getFilename() + "_Iteration" + mPrefs.getIteration();
					final String solverCommand;
					if (useNonlinearConstraints) {
						// solverCommand = "yices-smt2 --incremental";
						// solverCommand = "/home/matthias/ultimate/barcelogic/barcelogic-NIRA -tlimit 5";
						solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
						// solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:1000";
					} else {
						// solverCommand = "yices-smt2 --incremental";
						solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
					}
					final boolean fakeNonIncrementalSolver = false;
					final Settings settings = new Settings(fakeNonIncrementalSolver, true, solverCommand, -1, null,
							dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
					traceChecker = new InterpolatingTraceCheckerPathInvariantsWithFallback(truePredicate,
							falsePredicate, new TreeMap<Integer, IPredicate>(),
							(NestedRun<CodeBlock, IPredicate>) mCounterexample, mCfgSmtToolkit,
							assertCodeBlocksIncrementally, mServices, mPrefs.getToolchainStorage(), true,
							mPredicateUnifier, useNonlinearConstraints, useVarsFromUnsatCore, settings,
							xnfConversionTechnique, simplificationTechnique,
							icfgContainer.getBoogie2SMT().getAxioms());
					break;
				default:
					throw new UnsupportedOperationException("unsupported interpolation");
			}
			mPrefs.getCegarLoopBenchmark().addTraceCheckerData(traceChecker.getTraceCheckerBenchmark());
			return traceChecker;
		}
	}
}
