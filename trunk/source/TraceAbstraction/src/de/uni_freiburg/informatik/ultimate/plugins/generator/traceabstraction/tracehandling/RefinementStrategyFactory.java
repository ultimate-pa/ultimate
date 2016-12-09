/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RefinementStrategyFactory {

	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPrefsConsolidation;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final CegarAbsIntRunner mAbsIntRunner;
	private final ILogger mLogger;
	private final IIcfg<?> mInitialIcfg;
	private final IToolchainStorage mStorage;
	private final PredicateFactory mPredicateFactory;
	private final AssertionOrderModulation mAssertionOrderModulation;

	public RefinementStrategyFactory(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaCheckAndRefinementPreferences prefs, final CegarAbsIntRunner absIntRunner,
			final IIcfg<?> initialIcfg, final PredicateFactory predicateFactory) {
		mServices = services;
		mStorage = storage;
		mPrefsConsolidation = taPrefsForInterpolantConsolidation;
		mPrefs = prefs;
		mAbsIntRunner = absIntRunner;
		mLogger = logger;
		mInitialIcfg = initialIcfg;
		mPredicateFactory = predicateFactory;
		mAssertionOrderModulation = new AssertionOrderModulation();
	}

	public IRefinementStrategy createStrategy(final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction, final int iteration,
			final CegarLoopStatisticsGenerator benchmark) {

		final PredicateUnifier predicateUnifier = new PredicateUnifier(mServices,
				mPrefs.getCfgSmtToolkit().getManagedScript(), mPredicateFactory, mInitialIcfg.getSymboltable(),
				mPrefsConsolidation.getSimplificationTechnique(), mPrefsConsolidation.getXnfConversionTechnique());
		final ManagedScript managedScript =
				setupManagedScriptInternal(mServices, mPrefs, mInitialIcfg, mStorage, iteration);

		switch (mPrefs.getRefinementStrategy()) {
		case FIXED_PREFERENCES:
			return new FixedTraceAbstractionRefinementStrategy(mLogger, mPrefs, managedScript, mServices,
					predicateUnifier, counterexample, abstraction, mPrefsConsolidation, iteration, benchmark);
		case PENGUIN:
			return new PenguinRefinementStrategy(mLogger, mPrefs, mServices, predicateUnifier, counterexample,
					abstraction, mPrefsConsolidation, iteration, benchmark);
		case WALRUS:
			return new WalrusRefinementStrategy(mLogger, mPrefs, mServices, predicateUnifier,
					counterexample, abstraction, mPrefsConsolidation, iteration, benchmark);
		case TAIPAN:
			return new TaipanRefinementStrategy(mLogger, mServices, mPrefs, predicateUnifier, mAbsIntRunner,
					mAssertionOrderModulation, counterexample, abstraction, iteration, benchmark);
		default:
			throw new IllegalArgumentException(
					"Unknown refinement strategy specified: " + mPrefs.getRefinementStrategy());
		}
	}

	private static ManagedScript setupManagedScriptInternal(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final IIcfg<?> icfgContainer,
			final IToolchainStorage toolchainStorage, final int iteration) throws AssertionError {
		final ManagedScript managedScript;

		switch (prefs.getRefinementStrategy()) {
		case PENGUIN:
		case WALRUS:
		case TAIPAN:
			managedScript = null;
			break;
		case FIXED_PREFERENCES:
			managedScript = setupManagedScript(services, icfgContainer, toolchainStorage, iteration, prefs);
			break;
		default:
			throw new IllegalArgumentException("Unknown mode: " + prefs.getRefinementStrategy());
		}
		return managedScript;
	}

	private static ManagedScript setupManagedScript(final IUltimateServiceProvider services,
			final IIcfg<?> icfgContainer, final IToolchainStorage toolchainStorage, final int iteration,
			final TaCheckAndRefinementPreferences prefs) throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (prefs.getUseSeparateSolverForTracechecks()) {
			final String filename = icfgContainer.getIdentifier() + "_TraceCheck_Iteration" + iteration;
			final SolverMode solverMode = prefs.getSolverMode();
			final boolean fakeNonIncrementalSolver = prefs.getFakeNonIncrementalSolver();
			final String commandExternalSolver = prefs.getCommandExternalSolver();
			final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
			final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
			final Settings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
					fakeNonIncrementalSolver, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(services, toolchainStorage,
					prefs.getSolverMode(), solverSettings, false, false, prefs.getLogicForExternalSolver(),
					"TraceCheck_Iteration" + iteration);
			mgdScriptTc = new ManagedScript(services, tcSolver);
			final TermTransferrer tt = new TermTransferrer(tcSolver);
			for (final Term axiom : icfgContainer.getCfgSmtToolkit().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			mgdScriptTc = prefs.getCfgSmtToolkit().getManagedScript();
		}
		return mgdScriptTc;
	}

}
