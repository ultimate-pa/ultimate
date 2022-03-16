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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpgStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyModuleMcr;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class McrRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	public McrRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist, final StrategyFactory<L> strategyFactory) {
		super(factory, createModules(factory, strategyFactory), exceptionBlacklist);
	}

	@SuppressWarnings("unchecked")
	private static final <L extends IIcfgTransition<?>> StrategyModules<L> createModules(
			final StrategyFactory<L>.StrategyModuleFactory factory, final StrategyFactory<L> strategyFactory) {
		final StrategyModuleMcr<L> mcrModule = factory.createStrategyModuleMcr(strategyFactory);
		final ITraceCheckStrategyModule<L, ?>[] traceChecks = new ITraceCheckStrategyModule[] { mcrModule };
		final IIpgStrategyModule<?, L>[] interpolantGenerators = new IIpgStrategyModule[] { mcrModule };
		final IIpAbStrategyModule<L> interpolantAutomatonBuilder = mcrModule;
		return new StrategyModules<>(traceChecks, interpolantGenerators, interpolantAutomatonBuilder);
	}

	@Override
	public String getName() {
		return RefinementStrategy.MCR.toString();
	}

	@Override
	protected boolean needsMoreInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		// we are only satisfied if we find perfect interpolants or run out of generators
		return perfectIpps.isEmpty();
	}
}
