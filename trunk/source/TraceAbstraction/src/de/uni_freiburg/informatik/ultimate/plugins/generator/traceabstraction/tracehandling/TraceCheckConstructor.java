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
import de.uni_freiburg.informatik.ultimate.lib.pdr.Pdr;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;

/**
 * On-demand trace checker constructor from given preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TraceCheckConstructor<LETTER extends IIcfgTransition<?>> implements Supplier<ITraceCheck> {
	private final ITraceCheckPreferences mPrefs;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IPredicate mPrecondition;
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
	public TraceCheckConstructor(final ITraceCheckPreferences prefs, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final IRun<LETTER, IPredicate, ?> counterexample,
			final IPredicate precondition, final InterpolationTechnique interpolationTechnique,
			final TaskIdentifier taskIdentifier) {
		this(prefs, managedScript, services, predicateFactory, predicateUnifier, counterexample, precondition,
				prefs.getAssertCodeBlocksOrder(), interpolationTechnique, taskIdentifier);
	}

	/**
	 * Copy constructor with different assertion order and interpolation technique
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
				other.mCounterexample, other.mPrecondition, assertOrder, interpolationTechnique, other.mTaskIdentifier);
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
	public TraceCheckConstructor(final ITraceCheckPreferences prefs, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition,
			final AssertCodeBlockOrder assertOrder, final InterpolationTechnique interpolationTechnique,
			final TaskIdentifier taskIdentifier) {
		mPrefs = prefs;
		mManagedScript = managedScript;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mCounterexample = counterexample;
		mPrecondition = precondition;
		mAssertionOrder = assertOrder;
		mInterpolationTechnique = interpolationTechnique;
		mTaskIdentifier = taskIdentifier;
	}

	@Override
	public ITraceCheck get() {
		final ITraceCheck traceCheck = constructTraceCheck();

		if (traceCheck.getToolchainCanceledExpection() != null) {
			throw traceCheck.getToolchainCanceledExpection();
		} else if (mPrefs.getUseSeparateSolverForTracechecks() && traceCheck.wasTracecheckFinishedNormally()) {
			mManagedScript.getScript().exit();
		}

		return traceCheck;
	}

	private ITraceCheck constructTraceCheck() {
		if (mInterpolationTechnique == null) {
			return constructDefault();
		}
		switch (mInterpolationTechnique) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			return constructCraig();
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
			return constructForwardBackward();
		case PathInvariants:
			return constructPathInvariants();
		case PDR:
			return constructPdr();
		default:
			throw new UnsupportedOperationException("unsupported interpolation: " + mInterpolationTechnique);
		}
	}

	private TraceCheck<LETTER> constructDefault() {
		final IPredicate postcondition = mPredicateUnifier.getFalsePredicate();

		return new TraceCheck<>(mPrecondition, postcondition, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()), mServices, mPrefs.getCfgSmtToolkit(), mAssertionOrder,
				mPrefs.computeCounterexample(), mPrefs.collectInterpolantStatistics());
	}

	private TraceCheck<LETTER> constructCraig() {
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		return new InterpolatingTraceCheckCraig<>(mPrecondition, falsePredicate, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()),
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(mCounterexample.getWord())), mServices,
				mPrefs.getCfgSmtToolkit(), mManagedScript, mPredicateFactory, mPredicateUnifier, mAssertionOrder,
				mPrefs.computeCounterexample(), mPrefs.collectInterpolantStatistics(), mInterpolationTechnique, true,
				xnfConversionTechnique, simplificationTechnique, false);
	}

	private TraceCheck<LETTER> constructForwardBackward() {
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		return new TraceCheckSpWp<>(mPrecondition, falsePredicate, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()), mPrefs.getCfgSmtToolkit(), mAssertionOrder,
				mPrefs.getUnsatCores(), mPrefs.getUseLiveVariables(), mServices, mPrefs.computeCounterexample(),
				mPredicateFactory, mPredicateUnifier, mInterpolationTechnique, mManagedScript, xnfConversionTechnique,
				simplificationTechnique,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(mCounterexample.getWord())),
				mPrefs.collectInterpolantStatistics());
	}

	private TraceCheck<LETTER> constructPathInvariants() {
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();

		final IIcfg<?> icfgContainer = mPrefs.getIcfgContainer();
		final boolean useNonlinearConstraints = mPrefs.getUseNonlinearConstraints();
		final boolean useUnsatCores = mPrefs.getUseVarsFromUnsatCore();
		final boolean useAbstractInterpretationPredicates = mPrefs.getUseAbstractInterpretation();
		final boolean useWpPredicates = mPrefs.getUseWeakestPreconditionForPathInvariants();
		final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript = mTaskIdentifier.toString();
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
		final SolverSettings solverSettings = new SolverSettings(fakeNonIncrementalSolver, true, solverCommand, -1, null,
				dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
		final InvariantSynthesisSettings invariantSynthesisSettings =
				new InvariantSynthesisSettings(solverSettings, useNonlinearConstraints, useUnsatCores,
						useAbstractInterpretationPredicates, useWpPredicates, true);

		return new InterpolatingTraceCheckPathInvariantsWithFallback<>(mPrecondition, falsePredicate,
				new TreeMap<Integer, IPredicate>(), (NestedRun<LETTER, IPredicate>) mCounterexample,
				mPrefs.getCfgSmtToolkit(), mAssertionOrder, mServices, mPrefs.getToolchainStorage(),
				mPrefs.computeCounterexample(), mPredicateFactory, mPredicateUnifier, invariantSynthesisSettings,
				xnfConversionTechnique, simplificationTechnique, icfgContainer, mPrefs.collectInterpolantStatistics());
	}

	private ITraceCheck constructPdr() {
		final IHoareTripleChecker htc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				HoareTripleChecks.MONOLITHIC, mPrefs.getCfgSmtToolkit(), mPredicateUnifier);
		final Pdr<LETTER> pdr = new Pdr<>(mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), mPrefs,
				mPredicateUnifier, htc, mCounterexample.getWord().asList());
		return pdr;
	}

}
