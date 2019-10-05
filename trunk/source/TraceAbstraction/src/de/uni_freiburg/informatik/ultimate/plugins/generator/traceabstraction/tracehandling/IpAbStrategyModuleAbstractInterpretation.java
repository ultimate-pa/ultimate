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

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class IpAbStrategyModuleAbstractInterpretation<LETTER extends IIcfgTransition<?>>
		implements IIpAbStrategyModule<LETTER> {

	private final IRun<LETTER, ?> mCounterexample;
	private final IPredicateUnifier mPredicateUnifier;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;

	private NestedWordAutomaton<LETTER, IPredicate> mAutomaton;
	private final IpTcStrategyModuleAbstractInterpretation<LETTER> mIpTcSmAbsInt;

	public IpAbStrategyModuleAbstractInterpretation(final IRun<LETTER, ?> counterexample,
			final IPredicateUnifier predicateUnifier,
			final IpTcStrategyModuleAbstractInterpretation<LETTER> ipTcSmAbsInt,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mIpTcSmAbsInt = ipTcSmAbsInt;
		mEmptyStackFactory = emptyStackFactory;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> buildInterpolantAutomaton(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mAutomaton == null) {
			mAutomaton = mIpTcSmAbsInt.getOrConstructRunner().createInterpolantAutomatonBuilder(mPredicateUnifier,
					mAutomaton, mCounterexample, mEmptyStackFactory).getResult();
		}
		return mAutomaton;
	}
}
