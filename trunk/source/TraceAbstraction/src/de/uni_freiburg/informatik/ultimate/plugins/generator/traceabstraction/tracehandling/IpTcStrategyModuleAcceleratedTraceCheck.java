/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.acceleratedtracecheck.AcceleratedTraceCheck;

/**
 * Creates {@link IInterpolatingTraceCheck} that uses loop acceleration.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleAcceleratedTraceCheck<L extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<IInterpolatingTraceCheck<L>, L> {

	private final IRun<L, ?> mCounterexample;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicateUnifier mPredicateUnifier;
	private final TaCheckAndRefinementPreferences<L> mPrefs;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final PredicateFactory mPredicateFactory;

	public IpTcStrategyModuleAcceleratedTraceCheck(final IUltimateServiceProvider services, final ILogger logger,
			final IRun<L, ?> counterexample, final IPredicate precondition, final IPredicate postcondition,
			final IPredicateUnifier predicateUnifier, final TaCheckAndRefinementPreferences<L> prefs,
			final PredicateFactory predicateFactory) {
		mServices = services;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mLogger = logger;
		mPrefs = prefs;
		mScript = mPrefs.getCfgSmtToolkit().getManagedScript();
		mPredicateFactory = predicateFactory;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IInterpolatingTraceCheck<L> construct() {
		return new AcceleratedTraceCheck<>(mServices, mLogger, mPrefs, mScript, mPredicateUnifier,
				(NestedRun<L, IPredicate>) mCounterexample, mPrecondition, mPostcondition, mPredicateFactory);
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		// no statistics yet
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

}
