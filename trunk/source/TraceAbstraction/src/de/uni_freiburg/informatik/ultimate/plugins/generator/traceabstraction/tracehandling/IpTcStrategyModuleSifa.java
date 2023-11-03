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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SifaRunner;

/**
 * Creates {@link IInterpolatingTraceCheck} using symbolic interpretation with fluid abstractions (SIFA).
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleSifa<LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<IInterpolatingTraceCheck<LETTER>, LETTER> {

	private final IRun<LETTER, ?> mCounterExample;
	private final IPredicateUnifier mPredicateUnifier;
	private final IIcfg<?> mIcfg;
	private final IUltimateServiceProvider mServices;

	private final ILogger mLogger;

	public IpTcStrategyModuleSifa(final IUltimateServiceProvider services, final ILogger logger, final IIcfg<?> icfg,
			final IRun<LETTER, ?> counterexample, final IPredicateUnifier predicateUnifier) {
		super();
		mServices = services;
		mLogger = logger;
		mIcfg = icfg;
		mCounterExample = counterexample;
		mPredicateUnifier = predicateUnifier;
	}

	@Override
	protected IInterpolatingTraceCheck<LETTER> construct() {
		return new SifaRunner<>(mServices, mLogger, mIcfg, mCounterExample, mPredicateUnifier);
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.SIFA, getOrConstruct().getStatistics());
	}

}
