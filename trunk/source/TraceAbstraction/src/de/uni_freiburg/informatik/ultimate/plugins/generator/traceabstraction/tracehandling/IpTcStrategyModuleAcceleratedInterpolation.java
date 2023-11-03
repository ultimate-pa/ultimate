/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolationCore.IStrategySupplier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

/**
 * Creates {@link IInterpolatingTraceCheck} using accelerated interpolation.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 *
 */
public class IpTcStrategyModuleAcceleratedInterpolation<L extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<IInterpolatingTraceCheck<L>, L> {

	private final IRun<L, ?> mCounterexample;
	private final IPredicateUnifier mPredicateUnifier;
	private final TaCheckAndRefinementPreferences<L> mPrefs;
	private final ILogger mLogger;
	private final Class<L> mTransitionClazz;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IStrategySupplier<L> mStrategySupplier;

	public IpTcStrategyModuleAcceleratedInterpolation(final IUltimateServiceProvider services, final ILogger logger,
			final IRun<L, ?> counterexample, final IPredicateUnifier predicateUnifier,
			final TaCheckAndRefinementPreferences<L> prefs, final IStrategySupplier<L> strategySupplier,
			final Class<L> transitionClazz) {
		mServices = services;
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mLogger = logger;
		mPrefs = prefs;
		mTransitionClazz = transitionClazz;
		mScript = mPrefs.getCfgSmtToolkit().getManagedScript();
		mStrategySupplier = strategySupplier;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IInterpolatingTraceCheck<L> construct() {
		return new AcceleratedInterpolation<>(mServices, mLogger, mPrefs, mScript, mPredicateUnifier,
				(IRun<L, IPredicate>) mCounterexample, mTransitionClazz, mPrefs.getLoopAccelerationTechnique(),
				mStrategySupplier);
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.ACCELERATED_INTERPOLATION,
				getOrConstruct().getStatistics());
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

}
