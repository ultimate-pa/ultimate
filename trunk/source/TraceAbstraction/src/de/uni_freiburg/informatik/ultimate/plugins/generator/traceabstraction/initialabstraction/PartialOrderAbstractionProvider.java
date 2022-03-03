/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderReductionFacade;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.IndependenceBuilder;

public class PartialOrderAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final PredicateFactory mPredicateFactory;
	private final PartialOrderMode mPartialOrderMode;
	private final OrderType mOrderType;
	private final long mDfsOrderSeed;

	public PartialOrderAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> stateFactory,
			final PredicateFactory predicateFactory, final PartialOrderMode partialOrderMode, final OrderType orderType,
			final long dfsOrderSeed) {
		this.mUnderlying = underlying;
		this.mServices = services;
		this.mStateFactory = stateFactory;
		this.mPredicateFactory = predicateFactory;
		this.mPartialOrderMode = partialOrderMode;
		this.mOrderType = orderType;
		this.mDfsOrderSeed = dfsOrderSeed;
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);

		// TODO recover these statistics
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		try {
			// setup POR depending on settings
			final IIndependenceRelation<IPredicate, L> indep = IndependenceBuilder
					.<L> semantic(mServices, icfg.getCfgSmtToolkit().getManagedScript(), false, false)
					.withSyntacticCheck().cached().threadSeparated().build();
			final PartialOrderReductionFacade<L> por = new PartialOrderReductionFacade<>(mServices, mPredicateFactory,
					icfg, errorLocs, mPartialOrderMode, mOrderType, mDfsOrderSeed, indep);

			// actually apply POR to automaton
			final NestedWordAutomaton<L, IPredicate> result = por.constructReduction(input, mStateFactory);

			por.reportStatistics();
			return result;
		} finally {
			// mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		}
	}

}
