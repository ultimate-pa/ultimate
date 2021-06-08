/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * A facade to simplify interaction with Partial Order Reduction, specifically in the context of verification.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters occurring in the automata that will be reduced.
 */
public class PartialOrderReductionFacade<L extends IAction> {
	public enum OrderType {
		BY_SERIAL_NUMBER, PSEUDO_LOCKSTEP, RANDOM, POSITIONAL_RANDOM
	}

	/**
	 * Indicates a kind of partial order reduction.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 */
	public enum PartialOrderMode {
		/**
		 * No partial order reduction is performed.
		 */
		NONE,
		/**
		 * Sleep set partial order reduction. Delay sets are used to handle loops, and the reduced automaton is a
		 * sub-structure of the input.
		 */
		SLEEP_DELAY_SET,
		/**
		 * Sleep set partial order reduction. Unrolling and splitting is performed to achieve a minimal reduction (in
		 * terms of the language). This duplicates states of the input automaton.
		 */
		SLEEP_NEW_STATES,
		/**
		 * Persistent set reduction.
		 */
		PERSISTENT_SETS,
		/**
		 * Combines persistent set reduction with {@link SLEEP_DELAY_SET}.
		 */
		PERSISTENT_SLEEP_DELAY_SET, PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER,
		/**
		 * Combines persistent set reduction with {@link SLEEP_NEW_STATES}.
		 */
		PERSISTENT_SLEEP_NEW_STATES, PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER,
	}

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;

	private final PartialOrderReductionFacade.PartialOrderMode mMode;
	private final IDfsOrder<L, IPredicate> mDfsOrder;
	private final IIndependenceRelation<IPredicate, L> mIndependence;
	private final ISleepSetStateFactory<L, IPredicate, IPredicate> mSleepFactory;
	private final IPersistentSetChoice<L, IPredicate> mPersistent;

	public PartialOrderReductionFacade(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs,
			final PartialOrderReductionFacade.PartialOrderMode mode,
			final PartialOrderReductionFacade.OrderType orderType, final long randomOrderSeed,
			final IIndependenceRelation<IPredicate, L> independence) {
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mMode = mode;
		mDfsOrder = getDfsOrder(orderType, randomOrderSeed);
		mIndependence = independence;
		mSleepFactory = getSleepFactory(predicateFactory);
		mPersistent = createPersistentSets(icfg, errorLocs);
	}

	private ISleepSetStateFactory<L, IPredicate, IPredicate> getSleepFactory(final PredicateFactory predicateFactory) {
		switch (mMode) {
		case NONE:
		case PERSISTENT_SETS:
			return null;
		case PERSISTENT_SLEEP_NEW_STATES:
		case SLEEP_NEW_STATES:
			return new SleepSetStateFactoryForRefinement<>(predicateFactory);
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
		case PERSISTENT_SLEEP_DELAY_SET:
		case SLEEP_DELAY_SET:
			return new ISleepSetStateFactory.NoUnrolling<>();
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);
		}
	}

	private static <L extends IAction> IDfsOrder<L, IPredicate>
			getDfsOrder(final PartialOrderReductionFacade.OrderType orderType, final long randomOrderSeed) {
		switch (orderType) {
		case BY_SERIAL_NUMBER:
			return ConstantDfsOrder.byHashCode();
		case PSEUDO_LOCKSTEP:
			return new PseudoLockstepOrder<>();
		case RANDOM:
			return new RandomDfsOrder<>(randomOrderSeed, false);
		case POSITIONAL_RANDOM:
			return new RandomDfsOrder<>(randomOrderSeed, true);
		default:
			throw new UnsupportedOperationException("Unknown order type: " + orderType);
		}
	}

	private final IPersistentSetChoice<L, IPredicate> createPersistentSets(final IIcfg<?> icfg,
			final Collection<? extends IcfgLocation> errorLocs) {
		switch (mMode) {
		case PERSISTENT_SETS:
		case PERSISTENT_SLEEP_DELAY_SET:
		case PERSISTENT_SLEEP_NEW_STATES:
			return (IPersistentSetChoice<L, IPredicate>) new CachedPersistentSetChoice<>(new ThreadBasedPersistentSets(
					mServices, icfg, (IIndependenceRelation<IPredicate, IcfgEdge>) mIndependence, null, errorLocs));
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
			return (IPersistentSetChoice<L, IPredicate>) new CachedPersistentSetChoice<>(new ThreadBasedPersistentSets(
					mServices, icfg, (IIndependenceRelation<IPredicate, IcfgEdge>) mIndependence,
					(IDfsOrder<IcfgEdge, IPredicate>) mDfsOrder, errorLocs));
		case NONE:
		case SLEEP_DELAY_SET:
		case SLEEP_NEW_STATES:
			return null;
		default:
			throw new UnsupportedOperationException("unsupported POR mode");
		}
	}

	public IPersistentSetChoice<L, IPredicate> getPersistentSets() {
		return mPersistent;
	}

	public void apply(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IDfsVisitor<L, IPredicate> visitor) throws AutomataOperationCanceledException {
		switch (mMode) {
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(mAutomataServices, input, mSleepFactory, mIndependence, mDfsOrder, visitor);
			break;
		case SLEEP_NEW_STATES:
			new SleepSetNewStateReduction<>(mAutomataServices, input, mSleepFactory, mIndependence, mDfsOrder, visitor);
			break;
		case PERSISTENT_SETS:
			PersistentSetReduction.applyWithoutSleepSets(input, mDfsOrder, mPersistent, visitor);
			break;
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
		case PERSISTENT_SLEEP_DELAY_SET:
			PersistentSetReduction.applyDelaySetReduction(mAutomataServices, input, mIndependence, mDfsOrder,
					mPersistent, visitor);
			break;
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
		case PERSISTENT_SLEEP_NEW_STATES:
			PersistentSetReduction.applyNewStateReduction(mAutomataServices, input, mIndependence, mDfsOrder,
					mSleepFactory, mPersistent, visitor);
			break;
		case NONE:
			new DepthFirstTraversal<>(input, mDfsOrder, visitor);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);

		}
	}

	public AutomatonConstructingVisitor<L, IPredicate> createConstructionVisitor(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		switch (mMode) {
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
		case PERSISTENT_SLEEP_DELAY_SET:
		case SLEEP_DELAY_SET:
		case PERSISTENT_SETS:
		case NONE:
			return new AutomatonConstructingVisitor<>(input, mAutomataServices, emptyStackFactory);
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
		case PERSISTENT_SLEEP_NEW_STATES:
		case SLEEP_NEW_STATES:
			final SleepSetStateFactoryForRefinement<L> factory = (SleepSetStateFactoryForRefinement<L>) mSleepFactory;
			return new AutomatonConstructingVisitor<>(x -> input.isInitial(factory.getOriginalState(x)),
					x -> input.isFinal(factory.getOriginalState(x)), input.getVpAlphabet(), mAutomataServices,
					emptyStackFactory);
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);
		}
	}

	public void reportStatistics() {
		final StatisticsData data = new StatisticsData();
		data.aggregateBenchmarkData(mIndependence.getStatistics());
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_NAME, "Independence relation benchmarks", data));

		if (mPersistent != null) {
			final StatisticsData persistentData = new StatisticsData();
			persistentData.aggregateBenchmarkData(mPersistent.getStatistics());
			mServices.getResultService().reportResult(Activator.PLUGIN_ID,
					new StatisticsResult<>(Activator.PLUGIN_NAME, "Persistent set benchmarks", persistentData));
		}
	}
}
