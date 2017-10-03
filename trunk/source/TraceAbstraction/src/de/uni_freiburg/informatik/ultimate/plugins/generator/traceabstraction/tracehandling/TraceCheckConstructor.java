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

import java.util.TreeMap;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;

/**
 * On-demand trace checker constructor from given preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
class TraceCheckConstructor<LETTER extends IIcfgTransition<?>> implements Supplier<TraceCheck> {
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final PredicateFactory mPredicateFactory;
	private final PredicateUnifier mPredicateUnifier;
	private final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final InterpolationTechnique mInterpolationTechnique;
	private final TaskIdentifier mTaskIdentifier;
	private final AssertCodeBlockOrder mAssertionOrder;

	/**
	 * @param prefs
	 *            Preferences.
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @param cegarLoopBenchmark
	 *            CEGAR loop benchmark
	 */
	public TraceCheckConstructor(final TaCheckAndRefinementPreferences<LETTER> prefs, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final PredicateUnifier predicateUnifier, final IRun<LETTER, IPredicate, ?> counterexample,
			final InterpolationTechnique interpolationTechnique, final TaskIdentifier taskIdentifier) {
		this(prefs, managedScript, services, predicateFactory, predicateUnifier, counterexample,
				prefs.getAssertCodeBlocksOrder(), interpolationTechnique, taskIdentifier);
	}

	/**
	 * Copy constructor.
	 *
	 * @param other
	 *            other object to copy fields from
	 * @param managedScript
	 *            managed script
	 * @param interpolationTechnique
	 *            new interpolation technique
	 * @param benchmark
	 *            CEGAR loop benchmark
	 */
	public TraceCheckConstructor(final TraceCheckConstructor<LETTER> other, final ManagedScript managedScript,
			final InterpolationTechnique interpolationTechnique) {
		this(other, managedScript, other.mAssertionOrder, interpolationTechnique);
	}

	/**
	 * Copy constructor with assertion order.
	 *
	 * @param other
	 *            other object to copy fields from
	 * @param managedScript
	 *            managed script
	 * @param assertOrder
	 *            assertion order
	 * @param interpolationTechnique
	 *            new interpolation technique
	 * @param benchmark
	 *            CEGAR loop benchmark
	 */
	public TraceCheckConstructor(final TraceCheckConstructor<LETTER> other, final ManagedScript managedScript,
			final AssertCodeBlockOrder assertOrder, final InterpolationTechnique interpolationTechnique) {
		this(other.mPrefs, managedScript, other.mServices, other.mPredicateFactory, other.mPredicateUnifier,
				other.mCounterexample, assertOrder, interpolationTechnique, other.mTaskIdentifier);
	}

	/**
	 * Full constructor.
	 * 
	 * @param prefs
	 *            Preferences.
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param assertOrder
	 *            assertion order
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @param taskIdentifier
	 *            iteration in the CEGAR loop
	 * @param cegarLoopBenchmark
	 *            CEGAR loop benchmark
	 */
	public TraceCheckConstructor(final TaCheckAndRefinementPreferences<LETTER> prefs, final ManagedScript managedScript,
			final IUltimateServiceProvider services,final PredicateFactory predicateFactory,  final PredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate, ?> counterexample, final AssertCodeBlockOrder assertOrder,
			final InterpolationTechnique interpolationTechnique, final TaskIdentifier taskIdentifier) {
		mPrefs = prefs;
		mManagedScript = managedScript;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mCounterexample = counterexample;
		mAssertionOrder = assertOrder;
		mInterpolationTechnique = interpolationTechnique;
		mTaskIdentifier = taskIdentifier;
	}

	@Override
	public TraceCheck get() {
		final TraceCheck traceCheck;
		if (mInterpolationTechnique == null) {
			traceCheck = constructDefault();
		} else {
			switch (mInterpolationTechnique) {
			case Craig_NestedInterpolation:
			case Craig_TreeInterpolation:
				traceCheck = constructCraig();
				break;
			case ForwardPredicates:
			case BackwardPredicates:
			case FPandBP:
			case FPandBPonlyIfFpWasNotPerfect:
				traceCheck = constructForwardBackward();
				break;
			case PathInvariants:
				traceCheck = constructPathInvariants();
				break;
			default:
				throw new UnsupportedOperationException("unsupported interpolation");
			}
		}

		if (traceCheck.getToolchainCanceledExpection() != null) {
			throw traceCheck.getToolchainCanceledExpection();
		} else if (mPrefs.getUseSeparateSolverForTracechecks() && traceCheck.wasTracecheckFinished()) {
			mManagedScript.getScript().exit();
		}

		return traceCheck;
	}

	private TraceCheck constructDefault() {
		final IPredicate precondition = mPredicateUnifier.getTruePredicate();
		final IPredicate postcondition = mPredicateUnifier.getFalsePredicate();

		final TraceCheck traceCheck;
		traceCheck = new TraceCheck(precondition, postcondition, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()), mPrefs.getCfgSmtToolkit(), mAssertionOrder, mServices,
				true);
		return traceCheck;
	}

	private TraceCheck constructCraig() {
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		final TraceCheck traceCheck;
		traceCheck = new InterpolatingTraceCheckCraig(truePredicate, falsePredicate,
				new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()),
				mPrefs.getCfgSmtToolkit(), mAssertionOrder, mServices, true, mPredicateFactory, mPredicateUnifier, mInterpolationTechnique,
				mManagedScript, true, xnfConversionTechnique, simplificationTechnique,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(mCounterexample.getWord())), false);
		return traceCheck;
	}

	private TraceCheck constructForwardBackward() {
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		final TraceCheck traceCheck;
		traceCheck = new TraceCheckSpWp(truePredicate, falsePredicate, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()), mPrefs.getCfgSmtToolkit(), mAssertionOrder,
				mPrefs.getUnsatCores(), mPrefs.getUseLiveVariables(), mServices, true, mPredicateFactory, mPredicateUnifier,
				mInterpolationTechnique, mManagedScript, xnfConversionTechnique, simplificationTechnique,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(mCounterexample.getWord())));
		return traceCheck;
	}

	@SuppressWarnings("unchecked")
	private TraceCheck constructPathInvariants() {
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		final IIcfg<?> icfgContainer = mPrefs.getIcfgContainer();
		final boolean useNonlinearConstraints = mPrefs.getUseNonlinearConstraints();
		final boolean useUnsatCores = mPrefs.getUseVarsFromUnsatCore();
		final boolean useAbstractInterpretationPredicates = mPrefs.getUseAbstractInterpretation();
		final boolean useWeakestPrecondition = mPrefs.getUseWeakestPreconditionForPathInvariants();
		final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript = "InVarSynth_" + icfgContainer.getIdentifier() + "_Iteration" + mTaskIdentifier;
		final String solverCommand;
		if (useNonlinearConstraints) {
			// solverCommand = "yices-smt2 --incremental";
			// solverCommand = "/home/matthias/ultimate/barcelogic/barcelogic-NIRA -tlimit 5";
			solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:12000";
			// solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:1000";
		} else {
			// solverCommand = "yices-smt2 --incremental";
			solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:12000";
		}
		final boolean fakeNonIncrementalSolver = false;
		final Settings solverSettings = new Settings(fakeNonIncrementalSolver, true, solverCommand, -1, null,
				dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
		final InvariantSynthesisSettings invariantSynthesisSettings = new InvariantSynthesisSettings(solverSettings,
				useNonlinearConstraints, useUnsatCores, useAbstractInterpretationPredicates, useWeakestPrecondition, true);
		

		return new InterpolatingTraceCheckPathInvariantsWithFallback(truePredicate, falsePredicate,
				new TreeMap<Integer, IPredicate>(), (NestedRun<CodeBlock, IPredicate>) mCounterexample,
				mPrefs.getCfgSmtToolkit(), mAssertionOrder, mServices, mPrefs.getToolchainStorage(), true,
				mPredicateFactory, mPredicateUnifier, invariantSynthesisSettings, xnfConversionTechnique, simplificationTechnique, icfgContainer);
	}

}
