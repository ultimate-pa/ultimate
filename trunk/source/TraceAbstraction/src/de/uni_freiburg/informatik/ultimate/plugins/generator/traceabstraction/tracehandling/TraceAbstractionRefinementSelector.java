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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * Checks a trace for feasibility and, if infeasible, selects a refinement strategy, i.e., constructs an interpolant
 * automaton.<br>
 * This class is used in the {@link BasicCegarLoop}.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceAbstractionRefinementSelector
		implements IRefinementSelector<NestedWordAutomaton<CodeBlock, IPredicate>> {
	/* inputs */
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
	private final PredicateFactory mPredicateFactory;
	private final BoogieIcfgContainer mIcfgContainer;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IToolchainStorage mToolchainStorage;
	private final int mIteration;

	/* intermediate */
	private final TaCheckAndRefinementPreferences mPrefs;

	/* outputs */
	private IRefinementStrategy<NestedWordAutomaton<CodeBlock, IPredicate>> mStrategy;
	private final LBool mFeasibility;
	private final PredicateUnifier mPredicateUnifier;

	@SuppressWarnings("unchecked")
	public TraceAbstractionRefinementSelector(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final IInterpolantAutomatonEvaluator evaluator,
			final PredicateFactory predicateFactory, final BoogieIcfgContainer icfgContainer,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IToolchainStorage toolchainStorage, final TAPreferences taPrefsForInterpolantConsolidation,
			final int iteration, final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction) {
		// initialize fields
		mServices = services;
		mLogger = logger;
		mCounterexample = counterexample;
		mPrefs = prefs;
		mPredicateFactory = predicateFactory;
		mIcfgContainer = icfgContainer;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mToolchainStorage = toolchainStorage;
		mIteration = iteration;

		mPredicateUnifier = new PredicateUnifier(mServices, mPrefs.getCfgSmtToolkit().getManagedScript(),
				mPredicateFactory, mIcfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(), mSimplificationTechnique,
				mXnfConversionTechnique);

		// choose strategy
		mStrategy = chooseStrategy(abstraction, evaluator, taPrefsForInterpolantConsolidation);

		// check feasibility using the strategy
		mFeasibility = checkCounterexampleFeasibility();
		switch (mFeasibility) {
		case UNKNOWN:
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Strategy " + mStrategy.getClass().getSimpleName()
						+ " was unsuccessful and could not determine trace feasibility.");
			}
			mStrategy = new ProoflessRefinementStrategy(mStrategy.getTraceChecker());
			break;
		case UNSAT:
			break;
		case SAT:
			mStrategy = new ProoflessRefinementStrategy(mStrategy.getTraceChecker());
			break;
		default:
			throw new IllegalArgumentException("Unknown case: " + mFeasibility);
		}
	}

	@Override
	public LBool getCounterexampleFeasibility() {
		return mFeasibility;
	}

	@Override
	public RcfgProgramExecution getRcfgProgramExecution() {
		return mStrategy.getTraceChecker().getRcfgProgramExecution();
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getInfeasibilityProof() {
		return mStrategy.getInfeasibilityProof();
	}

	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	public CachingHoareTripleChecker getHoareTripleChecker() {
		if (mStrategy.getInterpolantGenerator() instanceof InterpolantConsolidation) {
			return ((InterpolantConsolidation) mStrategy.getInterpolantGenerator()).getHoareTripleChecker();
		}
		return null;
	}
	
	private IRefinementStrategy<NestedWordAutomaton<CodeBlock, IPredicate>> chooseStrategy(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantAutomatonEvaluator evaluator,
			final TAPreferences taPrefsForInterpolantConsolidation) {
		// TODO add options in preferences, currently we only try the FixedTraceAbstractionRefinementStrategy
		final ManagedScript managedScript = setupManagedScript();
		final IRefinementStrategy<NestedWordAutomaton<CodeBlock, IPredicate>> strategy =
				new FixedTraceAbstractionRefinementStrategy(mLogger, mPrefs, managedScript, mServices,
						mPredicateUnifier, mCounterexample, abstraction, evaluator, taPrefsForInterpolantConsolidation);
		return strategy;
	}

	private LBool checkCounterexampleFeasibility() {
		do {
			final LBool feasibility = mStrategy.getTraceChecker().isCorrect();
			// TODO add timeout check
			if (feasibility == LBool.UNKNOWN && mStrategy.hasNext()) {
				mStrategy.next();
				continue;
			}
			return feasibility;
		} while (true);
	}

	private ManagedScript setupManagedScript() throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (mPrefs.getUseSeparateSolverForTracechecks()) {
			final String filename = mIcfgContainer.getFilename() + "_TraceCheck_Iteration" + mIteration;
			final SolverMode solverMode = mPrefs.getSolverMode();
			final boolean fakeNonIncrementalSolver = mPrefs.getFakeNonIncrementalSolver();
			final String commandExternalSolver = mPrefs.getCommandExternalSolver();
			final boolean dumpSmtScriptToFile = mPrefs.getDumpSmtScriptToFile();
			final String pathOfDumpedScript = mPrefs.getPathOfDumpedScript();
			final Settings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
					fakeNonIncrementalSolver, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
					mPrefs.getSolverMode(), solverSettings, false, false, mPrefs.getLogicForExternalSolver(),
					"TraceCheck_Iteration" + mIteration);
			mgdScriptTc = new ManagedScript(mServices, tcSolver);
			final TermTransferrer tt = new TermTransferrer(tcSolver);
			for (final Term axiom : mIcfgContainer.getBoogie2SMT().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			mgdScriptTc = mPrefs.getCfgSmtToolkit().getManagedScript();
		}
		return mgdScriptTc;
	}
}
