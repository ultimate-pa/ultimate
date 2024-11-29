/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * Transforms an initial abstraction by applying one-shot Partial Order Reduction.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            the type of transitions
 */
public class PartialOrderAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final PredicateFactory mPredicateFactory;
	private final PartialOrderMode mPartialOrderMode;
	private final OrderType mOrderType;
	private final long mDfsOrderSeed;

	private final Statistics mStatistics = new Statistics();

	/**
	 * Create a new instance of the provider.
	 *
	 * @param underlying
	 *            The provider whose provided initial abstraction is then transformed by this instance
	 * @param services
	 *            Ultimate services used by Partial Order Reduction
	 * @param stateFactory
	 *            A state factory used by the reduced automaton
	 * @param predicateFactory
	 *            Predicate factory used to create predicate states for the reduced automaton
	 * @param partialOrderMode
	 *            The type of Partial Order Reduction that shall be applied
	 * @param orderType
	 *            Indicates the preference order used by Partial Order Reduction
	 * @param dfsOrderSeed
	 *            If {@code orderType} is random-based, the seed to use for the random generator.
	 * @param pluginId
	 *            Plugin ID used to report statistics
	 */
	public PartialOrderAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> stateFactory,
			final PredicateFactory predicateFactory, final PartialOrderMode partialOrderMode, final OrderType orderType,
			final long dfsOrderSeed) {
		mUnderlying = underlying;
		mServices = services;
		mStateFactory = stateFactory;
		mPredicateFactory = predicateFactory;
		mPartialOrderMode = partialOrderMode;
		mOrderType = orderType;
		mDfsOrderSeed = dfsOrderSeed;
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);

		// setup POR depending on settings
		final IIndependenceRelation<IPredicate, L> indep =
				IndependenceBuilder.<L> semantic(mServices, icfg.getCfgSmtToolkit().getManagedScript(), false, false)
						.withSyntacticCheck().cached().threadSeparated().build();
		final PartialOrderReductionFacade<L> por = new PartialOrderReductionFacade<>(mServices, mPredicateFactory, icfg,
				errorLocs, mPartialOrderMode, mOrderType, mDfsOrderSeed, List.of(indep), null, null);

		// actually apply POR to automaton
		final NestedWordAutomaton<L, IPredicate> result = por.constructReduction(input, mStateFactory);

		mStatistics.reportPORStatistics(por);
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private class Statistics extends AbstractStatisticsDataProvider {
		private static final String POR_STATISTICS = "Partial Order Reduction statistics";
		private static final String UNDERLYING_STATISTICS = "Statistics of underlying abstraction provider";

		public Statistics() {
			forward(UNDERLYING_STATISTICS, mUnderlying::getStatistics);
		}

		private void reportPORStatistics(final PartialOrderReductionFacade<?> por) {
			final var data = new StatisticsData();
			data.aggregateBenchmarkData(por.getStatistics());
			include(POR_STATISTICS, () -> data);
		}
	}
}
