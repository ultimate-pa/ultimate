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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode;

/**
 *
 * {@link IIpAbStrategyModule} that uses the {@link StraightLineInterpolantAutomatonBuilder} and all perfect
 * interpolants if there are any, or all imperfect interpolants.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class IpAbStrategyModuleStraightlineAll<LETTER> implements IIpAbStrategyModule<LETTER> {

	private final IUltimateServiceProvider mServices;
	private final Word<LETTER> mCounterexample;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;

	private IpAbStrategyModuleResult<LETTER> mResult;
	private final ILogger mLogger;

	public IpAbStrategyModuleStraightlineAll(final IUltimateServiceProvider services, final ILogger logger,
			final IAutomaton<LETTER, IPredicate> abstraction, final Word<LETTER> counterexample,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mServices = services;
		mLogger = logger;
		mAbstraction = abstraction;
		mCounterexample = counterexample;
		mEmptyStackFactory = emptyStackFactory;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		final List<QualifiedTracePredicates> usedIpps;
		final String logMsg;
		if (perfectIpps.isEmpty()) {
			usedIpps = imperfectIpps;
			logMsg = String.format("Using %s imperfect interpolants to construct interpolant automaton",
					usedIpps.size());
		} else {
			usedIpps = perfectIpps;
			logMsg = String.format("Using %s perfect interpolants to construct interpolant automaton", usedIpps.size());
		}
		mLogger.info(logMsg);
		if (mResult == null) {
			final StraightLineInterpolantAutomatonBuilder<LETTER> automatonBuilder =
					new StraightLineInterpolantAutomatonBuilder<>(mServices, mCounterexample,
							NestedWordAutomataUtils.getVpAlphabet(mAbstraction),
							QualifiedTracePredicates.toList(usedIpps), mEmptyStackFactory,
							InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING);
			final NestedWordAutomaton<LETTER, IPredicate> automaton = automatonBuilder.getResult();
			mResult = new IpAbStrategyModuleResult<>(automaton, usedIpps);
		}
		return mResult;
	}

}
