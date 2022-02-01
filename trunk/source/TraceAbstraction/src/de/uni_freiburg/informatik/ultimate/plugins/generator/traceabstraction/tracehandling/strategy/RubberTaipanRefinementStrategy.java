/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpgStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyModuleFactory;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class RubberTaipanRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	public RubberTaipanRefinementStrategy(final StrategyModuleFactory<L> factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory, createModules(factory), exceptionBlacklist);
	}

	@SuppressWarnings("unchecked")
	private static final <L extends IIcfgTransition<?>> StrategyModules<L>
			createModules(final StrategyModuleFactory<L> factory) {

		final IIpTcStrategyModule<?, L> smtinterpol =
				factory.createIpTcStrategyModuleSmtInterpolCraig(false, InterpolationTechnique.Craig_TreeInterpolation);
		final IIpTcStrategyModule<?, L> z3 = factory.createIpTcStrategyModuleZ3(false, InterpolationTechnique.FPandBP);
		final IIpTcStrategyModule<?, L> cvc4 = factory.createIpTcStrategyModuleCVC4(false,
				InterpolationTechnique.FPandBP, SolverBuilder.LOGIC_CVC4_DEFAULT);

		final ITraceCheckStrategyModule<L, ?>[] traceChecks = new ITraceCheckStrategyModule[] { smtinterpol, z3, cvc4 };
		final IIpgStrategyModule<?, L>[] interpolantGenerators = new IIpgStrategyModule[] { smtinterpol, z3, cvc4 };
		final IIpAbStrategyModule<L> interpolantAutomatonBuilder = factory.createIpAbStrategyModuleStraightlineAll();
		return new StrategyModules<>(traceChecks, interpolantGenerators, interpolantAutomatonBuilder);
	}

	@Override
	public String getName() {
		return RefinementStrategy.RUBBER_TAIPAN.toString();
	}

	@Override
	protected boolean needsMoreInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		// we are only satisfied if we find perfect interpolants or run out of generators
		return perfectIpps.isEmpty();
	}
}
