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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpgStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner.AbsIntInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class TaipanRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	public TaipanRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory, createModules(factory), exceptionBlacklist);
	}

	@SuppressWarnings("unchecked")
	private static final <L extends IIcfgTransition<?>> StrategyModules<L>
			createModules(final StrategyFactory<L>.StrategyModuleFactory factory) {

		final AssertCodeBlockOrder[] order = { AssertCodeBlockOrder.NOT_INCREMENTALLY,
				new AssertCodeBlockOrder(AssertCodeBlockOrderType.OUTSIDE_LOOP_FIRST2),
				new AssertCodeBlockOrder(AssertCodeBlockOrderType.TERMS_WITH_SMALL_CONSTANTS_FIRST) };

		final IIpTcStrategyModule<?, L> smtinterpol =
				factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation, order);
		final IIpTcStrategyModule<?, L> z3 = factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBP, order);
		final IIpTcStrategyModule<?, L> absint = factory.createIpTcStrategyModuleAbstractInterpretation();

		final ITraceCheckStrategyModule<L, ?>[] traceChecks = new ITraceCheckStrategyModule[] { smtinterpol, z3 };
		final IIpgStrategyModule<?, L>[] interpolantGenerators = new IIpgStrategyModule[] { smtinterpol, z3, absint };
		final IIpAbStrategyModule<L> interpolantAutomatonBuilder = factory.createIpAbStrategyModuleStraightlineAll();
		return new StrategyModules<>(traceChecks, interpolantGenerators, interpolantAutomatonBuilder);
	}

	@Override
	public String getName() {
		return RefinementStrategy.TAIPAN.toString();
	}

	@Override
	protected boolean needsMoreInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		// we are only satisfied if we find perfect interpolants or run out of generators
		return perfectIpps.isEmpty();
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker(final IRefinementEngine<L, ?> engine) {
		if (engine.getResult().getUsedTracePredicates().stream().allMatch(this::isAbsIntPredicate)) {
			// rather hacky: we now that the absint module is in position 2
			return getInterpolantGeneratorModules()[2].getHoareTripleChecker();
		}
		return super.getHoareTripleChecker(engine);
	}

	@Override
	public IPredicateUnifier getPredicateUnifier(final IRefinementEngine<L, ?> engine) {
		if (engine.getResult().getUsedTracePredicates().stream().allMatch(this::isAbsIntPredicate)) {
			// rather hacky: we know that the absint module is in position 2
			return getInterpolantGeneratorModules()[2].getPredicateUnifier();
		}
		return super.getPredicateUnifier(engine);
	}

	private boolean isAbsIntPredicate(final QualifiedTracePredicates qtp) {
		return qtp.getOrigin().isAssignableFrom(AbsIntInterpolantGenerator.class);
	}

	@Override
	public List<QualifiedTracePredicates> mergeInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		final List<QualifiedTracePredicates> perfectAbsIntIpps =
				perfectIpps.stream().filter(this::isAbsIntPredicate).collect(Collectors.toList());
		// If we have perfect interpolants from AbsInt, we use them
		if (!perfectAbsIntIpps.isEmpty()) {
			return perfectAbsIntIpps;
		}
		// Otherwise we use all interpolants that are not provided by AbsInt
		return Stream.concat(perfectIpps.stream(), imperfectIpps.stream()).filter(x -> !isAbsIntPredicate(x))
				.collect(Collectors.toList());
	}
}
