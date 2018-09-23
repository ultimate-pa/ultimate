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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;

/**
 * Wrapper for preferences of trace check and refinement selection module.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TaCheckAndRefinementPreferences<LETTER extends IIcfgTransition<?>> implements ITraceCheckPreferences {
	// fields that are provided in the constructor
	private final InterpolationTechnique mInterpolationTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final IIcfg<?> mIcfgContainer;
	private final IToolchainStorage mToolchainStorage;
	private final InterpolantAutomatonBuilderFactory<LETTER> mInterpolantAutomatonBuilderFactory;

	// fields that can be read from the TAPreferences
	private final RefinementStrategy mRefinementStrategy;
	private final boolean mUseSeparateSolverForTracechecks;
	private final SolverMode mSolverMode;
	private final boolean mFakeNonIncrementalSolver;
	private final String mCommandExternalSolver;
	private final boolean mDumpSmtScriptToFile;
	private final String mPathOfDumpedScript;
	private final String mLogicForExternalSolver;
	private final RefinementStrategyExceptionBlacklist mExceptionBlacklist;

	// fields that can be read from the IUltimateServiceProvider
	private final AssertCodeBlockOrder mAssertCodeBlocksOrder;
	private final UnsatCores mUnsatCores;
	private final boolean mUseLiveVariables;
	private final boolean mUseInterpolantConsolidation;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseVarsFromUnsatCoreForPathInvariants;
	private final boolean mUseWeakestPreconditionForPathInvariants;
	private final boolean mUseAbstractInterpretationPredicates;
	private final boolean mComputeCounterexample;
	private final boolean mCollectInterpolantStatistics;
	private final IUltimateServiceProvider mServices;
	private final boolean mUsePredicateTrieBasedPredicateUnifier;

	/**
	 * Constructor from existing trace abstraction and Ultimate preferences.
	 *
	 * @param services
	 *            Ultimate services
	 * @param taPrefs
	 *            trace abstraction preferences
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @param icfgContainer
	 *            ICFG container
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param cfgSmtToolkit
	 *            CFG-SMT toolkit
	 * @param predicateFactory
	 *            predicate factory
	 * @param toolchainStorage
	 *            toolchain storage
	 * @param interpolantAutomatonBuilderFactory
	 *            factory for interpolant automaton builder
	 */
	public TaCheckAndRefinementPreferences(final IUltimateServiceProvider services, final TAPreferences taPrefs,
			final InterpolationTechnique interpolationTechnique, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final IIcfg<?> icfgContainer,
			final IToolchainStorage toolchainStorage,
			final InterpolantAutomatonBuilderFactory<LETTER> interpolantAutomatonBuilderFactory) {
		mServices = services;
		mInterpolationTechnique = interpolationTechnique;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mIcfgContainer = icfgContainer;
		mToolchainStorage = toolchainStorage;
		mInterpolantAutomatonBuilderFactory = interpolantAutomatonBuilderFactory;

		mRefinementStrategy = taPrefs.getRefinementStrategy();
		mUseSeparateSolverForTracechecks = taPrefs.useSeparateSolverForTracechecks();
		mSolverMode = taPrefs.solverMode();
		mFakeNonIncrementalSolver = taPrefs.fakeNonIncrementalSolver();
		mCommandExternalSolver = taPrefs.commandExternalSolver();
		mDumpSmtScriptToFile = taPrefs.dumpSmtScriptToFile();
		mPathOfDumpedScript = taPrefs.pathOfDumpedScript();
		mLogicForExternalSolver = taPrefs.logicForExternalSolver();
		mExceptionBlacklist = taPrefs.getRefinementStrategyExceptionSpecification();
		mCollectInterpolantStatistics = taPrefs.collectInterpolantStatistics();

		final IPreferenceProvider ultimatePrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		mAssertCodeBlocksOrder =
				ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
						AssertCodeBlockOrder.class);
		mUnsatCores = ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mUseAbstractInterpretationPredicates = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ABSTRACT_INTERPRETATION_FOR_PATH_INVARIANTS);
		mUseInterpolantConsolidation =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		mUseNonlinearConstraints = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS);
		mUseVarsFromUnsatCoreForPathInvariants =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES_IN_PATHINVARIANTS);
		mUseWeakestPreconditionForPathInvariants = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_WEAKEST_PRECONDITION_IN_PATHINVARIANTS);
		mComputeCounterexample =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_COMPUTE_COUNTEREXAMPLE);
		mUsePredicateTrieBasedPredicateUnifier = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER);
	}

	public RefinementStrategy getRefinementStrategy() {
		return mRefinementStrategy;
	}

	@Override
	public boolean getUseSeparateSolverForTracechecks() {
		return mUseSeparateSolverForTracechecks;
	}

	public SolverMode getSolverMode() {
		return mSolverMode;
	}

	public boolean getFakeNonIncrementalSolver() {
		return mFakeNonIncrementalSolver;
	}

	public String getCommandExternalSolver() {
		return mCommandExternalSolver;
	}

	@Override
	public boolean getDumpSmtScriptToFile() {
		return mDumpSmtScriptToFile;
	}

	@Override
	public String getPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}

	public String getLogicForExternalSolver() {
		return mLogicForExternalSolver;
	}

	public InterpolationTechnique getInterpolationTechnique() {
		return mInterpolationTechnique;
	}

	@Override
	public SimplificationTechnique getSimplificationTechnique() {
		return mSimplificationTechnique;
	}

	@Override
	public XnfConversionTechnique getXnfConversionTechnique() {
		return mXnfConversionTechnique;
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
	}

	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	@Override
	public IIcfg<?> getIcfgContainer() {
		return mIcfgContainer;
	}

	@Override
	public IToolchainStorage getToolchainStorage() {
		return mToolchainStorage;
	}

	public InterpolantAutomatonBuilderFactory<LETTER> getInterpolantAutomatonBuilderFactory() {
		return mInterpolantAutomatonBuilderFactory;
	}

	@Override
	public AssertCodeBlockOrder getAssertCodeBlocksOrder() {
		return mAssertCodeBlocksOrder;
	}

	@Override
	public UnsatCores getUnsatCores() {
		return mUnsatCores;
	}

	@Override
	public boolean getUseLiveVariables() {
		return mUseLiveVariables;
	}

	@Override
	public boolean getUseAbstractInterpretation() {
		return mUseAbstractInterpretationPredicates;
	}

	public boolean getUseInterpolantConsolidation() {
		return mUseInterpolantConsolidation;
	}

	@Override
	public boolean getUseNonlinearConstraints() {
		return mUseNonlinearConstraints;
	}

	@Override
	public boolean getUseVarsFromUnsatCore() {
		return mUseVarsFromUnsatCoreForPathInvariants;
	}

	@Override
	public boolean getUseWeakestPreconditionForPathInvariants() {
		return mUseWeakestPreconditionForPathInvariants;
	}

	@Override
	public boolean computeCounterexample() {
		return mComputeCounterexample;
	}

	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mExceptionBlacklist;
	}

	@Override
	public boolean collectInterpolantStatistics() {
		return mCollectInterpolantStatistics;
	}

	@Override
	public IUltimateServiceProvider getUltimateServices() {
		return mServices;
	}

	public boolean usePredicateTrieBasedPredicateUnifier() {
		return mUsePredicateTrieBasedPredicateUnifier;
	}
}
