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
import java.util.Comparator;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.MinimalSleepSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * A facade to simplify interaction with Partial Order Reduction, specifically in the context of verification.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters occurring in the automata that will be reduced.
 */
public class PartialOrderReductionFacade<L extends IIcfgTransition<?>> {
	public enum OrderType {
		BY_SERIAL_NUMBER, PSEUDO_LOCKSTEP, RANDOM, POSITIONAL_RANDOM, LOOP_LOCKSTEP
	}

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;

	private final PartialOrderMode mMode;
	private final IDfsOrder<L, IPredicate> mDfsOrder;
	private final IIndependenceRelation<IPredicate, L> mIndependence;
	private final ISleepSetStateFactory<L, IPredicate, IPredicate> mSleepFactory;
	private final IPersistentSetChoice<L, IPredicate> mPersistent;

	public PartialOrderReductionFacade(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs, final PartialOrderMode mode,
			final OrderType orderType, final long randomOrderSeed,
			final IIndependenceRelation<IPredicate, L> independence) {
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mMode = mode;
		mSleepFactory = createSleepFactory(predicateFactory);
		mDfsOrder = getDfsOrder(orderType, randomOrderSeed, icfg, errorLocs);
		mIndependence = independence;
		mPersistent = createPersistentSets(icfg, errorLocs);
	}

	private ISleepSetStateFactory<L, IPredicate, IPredicate>
			createSleepFactory(final PredicateFactory predicateFactory) {
		if (!mMode.hasSleepSets()) {
			return null;
		}
		if (mMode.doesUnrolling()) {
			return new SleepSetStateFactoryForRefinement<>(predicateFactory);
		}
		return new ISleepSetStateFactory.NoUnrolling<>();
	}

	public ISleepSetStateFactory<L, IPredicate, IPredicate> getSleepFactory() {
		return mSleepFactory;
	}

	private IDfsOrder<L, IPredicate> getDfsOrder(final OrderType orderType, final long randomOrderSeed,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs) {
		switch (orderType) {
		case BY_SERIAL_NUMBER:
			final Set<String> errorThreads =
					errorLocs.stream().map(IcfgLocation::getProcedure).collect(Collectors.toSet());
			return new ConstantDfsOrder<>(
					Comparator.<L, Boolean> comparing(x -> !errorThreads.contains(x.getPrecedingProcedure()))
							.thenComparing(Comparator.comparingInt(Object::hashCode)));
		case PSEUDO_LOCKSTEP:
			return new BetterLockstepOrder<>(this::normalizePredicate);
		case RANDOM:
			return new RandomDfsOrder<>(randomOrderSeed, false);
		case POSITIONAL_RANDOM:
			return new RandomDfsOrder<>(randomOrderSeed, true, this::normalizePredicate);
		case LOOP_LOCKSTEP:
			if (mSleepFactory instanceof SleepSetStateFactoryForRefinement<?>) {
				return new LoopLockstepOrder<>(icfg,
						((SleepSetStateFactoryForRefinement<?>) mSleepFactory)::getOriginalState);
			}
			return new LoopLockstepOrder<>(icfg, null);
		default:
			throw new UnsupportedOperationException("Unknown order type: " + orderType);
		}
	}

	private final IPersistentSetChoice<L, IPredicate> createPersistentSets(final IIcfg<?> icfg,
			final Collection<? extends IcfgLocation> errorLocs) {
		if (!mMode.hasPersistentSets()) {
			return null;
		}

		final IIndependenceRelation<IPredicate, L> independence =
				IndependenceBuilder.fromIndependence(mIndependence).ensureUnconditional().build();
		final IDfsOrder<IcfgEdge, IPredicate> relevantOrder =
				mMode.hasFixedOrder() ? (IDfsOrder<IcfgEdge, IPredicate>) mDfsOrder : null;

		return (IPersistentSetChoice<L, IPredicate>) new CachedPersistentSetChoice<>(
				new ThreadBasedPersistentSets<>(mServices, icfg,
						(IIndependenceRelation<IPredicate, IcfgEdge>) independence, relevantOrder, errorLocs),
				this::normalizePredicate);
	}

	private Object normalizePredicate(final IPredicate state) {
		if (mMode.hasFixedOrder() && mDfsOrder instanceof LoopLockstepOrder<?>) {
			// For stateful orders, we need to include the chosen order in the normalization if we want to guarantee
			// compatibility of persistent sets.
			return new Pair<>(((IMLPredicate) state).getProgramPoints(), mDfsOrder.getOrder(state));
		}
		return ((IMLPredicate) state).getProgramPoints();
	}

	public IPersistentSetChoice<L, IPredicate> getPersistentSets() {
		return mPersistent;
	}

	public IDfsOrder<L, IPredicate> getDfsOrder() {
		return mDfsOrder;
	}

	/**
	 * Apply POR to a given automaton.
	 *
	 * @param input
	 *            The automaton to which reduction is applied
	 * @param visitor
	 *            A visitor that traverses the reduced automaton
	 * @throws AutomataOperationCanceledException
	 */
	public void apply(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IDfsVisitor<L, IPredicate> visitor) throws AutomataOperationCanceledException {
		if (mDfsOrder instanceof LoopLockstepOrder<?>) {
			input = ((LoopLockstepOrder<L>) mDfsOrder).wrapAutomaton(input);
		}

		switch (mMode) {
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(mAutomataServices, input, mSleepFactory, mIndependence, mDfsOrder, visitor);
			break;
		case SLEEP_NEW_STATES:
			new DepthFirstTraversal<>(mAutomataServices,
					new MinimalSleepSetReduction<>(input, mSleepFactory, mIndependence, mDfsOrder), mDfsOrder, visitor);
			break;
		case PERSISTENT_SETS:
			PersistentSetReduction.applyWithoutSleepSets(mAutomataServices, input, mDfsOrder, mPersistent, visitor);
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
			new DepthFirstTraversal<>(mAutomataServices, input, mDfsOrder, visitor);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);
		}
	}

	/**
	 * Creates a {@link DeadEndOptimizingSearchVisitor} suitable for use with this instance.
	 *
	 * @param <V>
	 *            The type of underlying visitor
	 * @param createUnderlying
	 *            A method to create the underlying visitor. See
	 *            {@link DeadEndOptimizingSearchVisitor#DeadEndOptimizingSearchVisitor(Supplier)} for details.
	 * @return the new visitor
	 */
	public <V extends IDfsVisitor<L, IPredicate>> DeadEndOptimizingSearchVisitor<L, IPredicate, IPredicate, V>
			createDeadEndVisitor(final Supplier<V> createUnderlying) {

		Function<IPredicate, IPredicate> getOriginal = null;
		Function<IPredicate, Object> getExtraInfo = null;
		boolean needsSplitting = false;

		if (mSleepFactory instanceof SleepSetStateFactoryForRefinement<?>) {
			final SleepSetStateFactoryForRefinement<L> refFactory =
					(SleepSetStateFactoryForRefinement<L>) mSleepFactory;
			getExtraInfo = addExtraInfo(getOriginal, getExtraInfo, refFactory::getSleepSet);
			getOriginal = andThenWithNullCheck(getOriginal, refFactory::getOriginalState);
			needsSplitting = true;
		}

		if (mDfsOrder instanceof LoopLockstepOrder<?>) {
			getExtraInfo = addExtraInfo(getOriginal, getExtraInfo, x -> ((PredicateWithLastThread) x).getLastThread());
			getOriginal = andThenWithNullCheck(getOriginal, x -> ((PredicateWithLastThread) x).getUnderlying());
			needsSplitting = true;
		}

		if (needsSplitting) {
			return new DeadEndOptimizingSearchVisitor<>(createUnderlying, getOriginal, getExtraInfo);
		}
		return new DeadEndOptimizingSearchVisitor<>(createUnderlying);
	}

	private static <T> Function<T, T> andThenWithNullCheck(final Function<T, T> first, final Function<T, T> second) {
		if (first == null) {
			return second;
		}
		if (second == null) {
			return first;
		}
		return first.andThen(second);
	}

	private static <T> Function<T, Object> addExtraInfo(final Function<T, T> getOriginal,
			final Function<T, Object> oldGetInfo, final Function<T, Object> getExtra) {
		if (oldGetInfo == null && getOriginal == null) {
			return getExtra;
		}
		if (oldGetInfo == null) {
			return getOriginal.andThen(getExtra);
		}
		return x -> new Pair<>(oldGetInfo.apply(x), getExtra.apply(getOriginal.apply(x)));
	}

	/**
	 * Constructs the reduced automaton explicitly.
	 *
	 * @param input
	 *            The automaton to be reduced.
	 * @param emptyStackFactory
	 *            A state factory used for the reduced automaton.
	 * @return An explicit representation of the reduced automaton
	 * @throws AutomataOperationCanceledException
	 *             in case of cancellation or timeout
	 */
	public NestedWordAutomaton<L, IPredicate> constructReduction(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) throws AutomataOperationCanceledException {
		if (mDfsOrder instanceof LoopLockstepOrder<?>) {
			// TODO Add support for detecting initial and final states in this case, similar to #createDeadEndVisitor
			throw new UnsupportedOperationException();
		}

		final AutomatonConstructingVisitor<L, IPredicate> visitor;
		if (mMode.hasSleepSets() && mMode.doesUnrolling()) {
			final SleepSetStateFactoryForRefinement<L> factory = (SleepSetStateFactoryForRefinement<L>) mSleepFactory;
			visitor = new AutomatonConstructingVisitor<>(x -> input.isInitial(factory.getOriginalState(x)),
					x -> input.isFinal(factory.getOriginalState(x)), input.getVpAlphabet(), mAutomataServices,
					emptyStackFactory);
		} else {
			visitor = new AutomatonConstructingVisitor<>(input, mAutomataServices, emptyStackFactory);
		}
		apply(input, visitor);
		return visitor.getReductionAutomaton();
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
