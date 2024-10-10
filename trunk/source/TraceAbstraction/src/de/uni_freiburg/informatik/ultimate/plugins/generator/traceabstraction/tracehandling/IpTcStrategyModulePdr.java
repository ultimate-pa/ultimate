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

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.pdr.Pdr;

/**
 * Creates {@link IInterpolatingTraceCheck} using {@link Pdr}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModulePdr<L extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<IInterpolatingTraceCheck<L>, L> {

	private final Word<L> mCounterExample;
	private final IPredicateUnifier mPredicateUnifier;
	private final TaCheckAndRefinementPreferences<L> mPrefs;
	private final ILogger mLogger;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final Class<L> mTransitionClazz;
	private final IUltimateServiceProvider mServices;

	public IpTcStrategyModulePdr(final IUltimateServiceProvider services, final ILogger logger,
			final IPredicate precondition, final IPredicate postcondition, final Word<L> counterexample,
			final IPredicateUnifier predicateUnifier, final TaCheckAndRefinementPreferences<L> prefs,
			final Class<L> transitionClazz) {
		mServices = services;
		mCounterExample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mLogger = logger;
		mPrefs = prefs;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mTransitionClazz = transitionClazz;
	}

	@Override
	protected IInterpolatingTraceCheck<L> construct() {
		return new Pdr<>(mServices, mLogger, mPrefs, mPredicateUnifier, mPrecondition, mPostcondition,
				mCounterExample.asList(), mTransitionClazz);
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.PDR, getOrConstruct().getStatistics());
	}

}
