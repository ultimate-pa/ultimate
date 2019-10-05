/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.pdr.Pdr;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;

/**
 * Creates a {@link IInterpolatingTraceCheck} based on the current preferences.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class IpTcStrategyModulePreferences<LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleTraceCheck<IInterpolatingTraceCheck<LETTER>, LETTER> {

	private final InterpolationTechnique mInterpolationTechnique;
	private final Logics mLogics;

	public IpTcStrategyModulePreferences(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final IRun<LETTER, ?> counterExample,
			final IPredicate precondition, final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory) {
		super(taskIdentifier, services, prefs, counterExample, precondition, assertionOrderModulation, predicateUnifier,
				predicateFactory);
		mInterpolationTechnique = mPrefs.getInterpolationTechnique();
		if (mInterpolationTechnique == null) {
			throw new UnsupportedOperationException("Cannot interpolate without a technique");
		}
		mLogics = Logics.valueOf(mPrefs.getLogicForExternalSolver());
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IInterpolatingTraceCheck<LETTER> construct() {
		final AssertCodeBlockOrder assertionOrder =
				mAssertionOrderModulation.get(mCounterexample, mInterpolationTechnique);
		final IPredicate postcondition = mPredicateUnifier.getFalsePredicate();
		final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
		final TreeMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final NestedWord<LETTER> nestedWord = NestedWord.nestedWord(mCounterexample.getWord());
		final List<IcfgLocation> sequenceOfProgramPoints = TraceCheckUtils.getSequenceOfProgramPoints(nestedWord);

		final ManagedScript managedScript = constructManagedScript();

		switch (mInterpolationTechnique) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			final boolean instanticateArrayExt = true;
			final boolean innerRecursiveNestedInterpolationCall = false;
			return new InterpolatingTraceCheckCraig<>(mPrecondition, postcondition, pendingContexts, nestedWord,
					sequenceOfProgramPoints, mServices, mPrefs.getCfgSmtToolkit(), managedScript, mPredicateFactory,
					mPredicateUnifier, assertionOrder, mPrefs.computeCounterexample(),
					mPrefs.collectInterpolantStatistics(), mInterpolationTechnique, instanticateArrayExt,
					xnfConversionTechnique, simplificationTechnique, innerRecursiveNestedInterpolationCall);
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
			return new TraceCheckSpWp<>(mPrecondition, postcondition, pendingContexts, nestedWord,
					mPrefs.getCfgSmtToolkit(), assertionOrder, mPrefs.getUnsatCores(), mPrefs.getUseLiveVariables(),
					mServices, mPrefs.computeCounterexample(), mPredicateFactory, mPredicateUnifier,
					mInterpolationTechnique, managedScript, xnfConversionTechnique, simplificationTechnique,
					sequenceOfProgramPoints, mPrefs.collectInterpolantStatistics());
		case PathInvariants:
			final IIcfg<?> icfgContainer = mPrefs.getIcfgContainer();
			final boolean useNonlinearConstraints = mPrefs.getUseNonlinearConstraints();
			final boolean useUnsatCores = mPrefs.getUseVarsFromUnsatCore();
			final boolean useAbstractInterpretationPredicates = mPrefs.getUseAbstractInterpretation();
			final boolean useWpPredicates = mPrefs.getUseWeakestPreconditionForPathInvariants();
			final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
			final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
			final String baseNameOfDumpedScript = mTaskIdentifier.toString();
			final String solverCommand = SolverBuilder.COMMAND_Z3_TIMEOUT;
			final boolean fakeNonIncrementalSolver = false;
			final SolverSettings solverSettings = new SolverSettings(fakeNonIncrementalSolver, true, solverCommand, -1,
					null, dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
			final InvariantSynthesisSettings invariantSynthesisSettings = new InvariantSynthesisSettings(solverSettings,
					useNonlinearConstraints, useUnsatCores, useAbstractInterpretationPredicates, useWpPredicates, true);

			return new InterpolatingTraceCheckPathInvariantsWithFallback<>(mPrecondition, postcondition,
					pendingContexts, (NestedRun<LETTER, IPredicate>) mCounterexample, mPrefs.getCfgSmtToolkit(),
					assertionOrder, mServices, mPrefs.computeCounterexample(), mPredicateFactory, mPredicateUnifier,
					invariantSynthesisSettings, xnfConversionTechnique, simplificationTechnique, icfgContainer,
					mPrefs.collectInterpolantStatistics());
		case PDR:
			return new Pdr<>(mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), mPrefs, mPredicateUnifier,
					mCounterexample.getWord().asList());
		case MCR:
			return new MCR<>(mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), mPrefs, mPredicateUnifier,
					constructHoareTripleChecker(), mCounterexample.getWord().asList());
		default:
			throw new UnsupportedOperationException("Unsupported interpolation technique: " + mInterpolationTechnique);
		}

	}

	private IHoareTripleChecker constructHoareTripleChecker() throws AssertionError {
		return TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				HoareTripleChecks.MONOLITHIC, mPrefs.getCfgSmtToolkit(), mPredicateUnifier);
	}

	private ManagedScript constructManagedScript() throws AssertionError {
		if (mInterpolationTechnique == InterpolationTechnique.PathInvariants) {
			// Path invariants construct their own solver
			return null;
		}
		if (mPrefs.getUseSeparateSolverForTracechecks()) {
			final SolverSettings solverSettings = constructSolverSettings();
			final boolean dumpUsatCoreTrackBenchmark = false;
			final boolean dumpMainTrackBenchmark = false;
			final String solderId = solverSettings.getBaseNameOfDumpedScript();
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, mPrefs.getSolverMode(),
					solverSettings, dumpUsatCoreTrackBenchmark, dumpMainTrackBenchmark, mLogics, solderId);

			final ManagedScript mgdScriptTc = new ManagedScript(mServices, tcSolver);

			mPrefs.getIcfgContainer().getCfgSmtToolkit().getSmtFunctionsAndAxioms().transferSymbols(tcSolver);

			return mgdScriptTc;
		}
		return mPrefs.getCfgSmtToolkit().getManagedScript();
	}

	private SolverSettings constructSolverSettings() throws AssertionError {
		final String filename = mTaskIdentifier + "_TraceCheck";
		final SolverMode solverMode = mPrefs.getSolverMode();
		final boolean fakeNonIncrementalSolver = mPrefs.getFakeNonIncrementalSolver();
		final String commandExternalSolver = mPrefs.getCommandExternalSolver();
		final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
		return SolverBuilder.constructSolverSettings(filename, solverMode, fakeNonIncrementalSolver,
				commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
	}
}
