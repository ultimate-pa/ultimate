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

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;

/**
 * Base class for all {@link IpTcStrategyModuleBase} implementations that create an {@link IInterpolatingTraceCheck}
 * using one of the instances of the {@link TraceCheck} family.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class IpTcStrategyModuleTraceCheck<T extends IInterpolatingTraceCheck<LETTER>, LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<T, LETTER> {

	protected final TaskIdentifier mTaskIdentifier;
	protected final IUltimateServiceProvider mServices;
	protected final TaCheckAndRefinementPreferences<?> mPrefs;
	protected final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	protected final Word<LETTER> mCounterexample;
	protected final List<?> mControlConfigurationSequence;
	protected final IPredicateUnifier mPredicateUnifier;
	protected final IPredicate mPrecondition;
	protected final IPredicate mPostcondition;
	protected final PredicateFactory mPredicateFactory;

	public IpTcStrategyModuleTraceCheck(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final Word<LETTER> counterExample,
			final List<?> controlConfigurationSequence, final IPredicate precondition, final IPredicate postcondition,
			final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
			final PredicateFactory predicateFactory) {
		mServices = services;
		mPrefs = prefs;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterExample;
		mControlConfigurationSequence = controlConfigurationSequence;
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = predicateFactory;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mTaskIdentifier = taskIdentifier;
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.TRACE_CHECK, getOrConstruct().getStatistics());
	}

	protected ManagedScript createExternalManagedScript(final SolverSettings solverSettings) {
		return mPrefs.getIcfgContainer().getCfgSmtToolkit().createFreshManagedScript(mServices, solverSettings,
				getSolverName());
	}

	/**
	 * For a given timeout, compare with {@link IProgressMonitorService}s timeout and return the more restrictive one.
	 *
	 * @param timeoutInMillis
	 *            The given timeout in milliseconds
	 * @return A non-negative timeout in milliseconds or -1 if there is no timeout.
	 */
	protected long computeTimeout(final long timeoutInMillis) {
		if (timeoutInMillis < 0 && timeoutInMillis != -1) {
			throw new IllegalArgumentException("timeout must be non-negative or -1");
		}
		final long remainingTime = mServices.getProgressMonitorService().remainingTime();
		if (timeoutInMillis == -1) {
			return remainingTime;
		}
		if (remainingTime == -1) {
			return timeoutInMillis;
		}
		return Math.min(remainingTime, timeoutInMillis);
	}

	private String getSolverName() {
		return "TraceCheck_Iteration_" + mTaskIdentifier.toString();
	}
}
