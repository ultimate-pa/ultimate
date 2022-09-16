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

import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantconsolidation.InterpolatingTraceCheckWithConsolidation;

/**
 * Creates separate instance of SmtInterpol with {@link InterpolationTechnique#Craig_NestedInterpolation} and without
 * timeout.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleInterpolantConsolidation<T extends IInterpolatingTraceCheck<L>, L extends IIcfgTransition<?>>
		implements IIpTcStrategyModule<InterpolatingTraceCheckWithConsolidation<T, L>, L> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final PredicateFactory mPredicateFactory;
	private final IIpTcStrategyModule<T, L> mIpTcModule;

	private InterpolatingTraceCheckWithConsolidation<T, L> mInterpolantConsolidation;

	public IpTcStrategyModuleInterpolantConsolidation(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<L> prefs, final PredicateFactory predicateFactory,
			final IIpTcStrategyModule<T, L> nestedModule) {
		mServices = services;
		mPrefs = prefs;
		mPredicateFactory = predicateFactory;
		mIpTcModule = nestedModule;
		mLogger = logger;
	}

	@Override
	public LBool isCorrect() {
		return mIpTcModule.isCorrect();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIpTcModule.providesRcfgProgramExecution();
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		return mIpTcModule.getRcfgProgramExecution();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mIpTcModule.getTraceCheckReasonUnknown();
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		return mIpTcModule.getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mIpTcModule.getPredicateUnifier();
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		mIpTcModule.aggregateStatistics(stats);
		stats.addStatistics(RefinementEngineStatisticsDefinitions.INTERPOLANT_CONSOLIDATION,
				getOrConstruct().getStatistics());
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return getOrConstruct().getInterpolantComputationStatus();
	}

	@Override
	public Collection<QualifiedTracePredicates> getPerfectInterpolantSequences() {
		final InterpolatingTraceCheckWithConsolidation<T, L> tc = getOrConstruct();
		if (tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), true));
		}
		return Collections.emptyList();
	}

	@Override
	public Collection<QualifiedTracePredicates> getImperfectInterpolantSequences() {
		final InterpolatingTraceCheckWithConsolidation<T, L> tc = getOrConstruct();
		if (!tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), false));
		}
		return Collections.emptyList();
	}

	@Override
	public InterpolatingTraceCheckWithConsolidation<T, L> getOrConstruct() {
		if (mInterpolantConsolidation == null) {
			final CfgSmtToolkit cfgSmtToolkit = mPrefs.getCfgSmtToolkit();
			try {
				mInterpolantConsolidation = new InterpolatingTraceCheckWithConsolidation<>(cfgSmtToolkit, mServices,
						mLogger, mPredicateFactory, mIpTcModule.getOrConstruct());
			} catch (final AutomataOperationCanceledException e) {
				throw new RuntimeException(e);
			}
		}
		return mInterpolantConsolidation;
	}
}
