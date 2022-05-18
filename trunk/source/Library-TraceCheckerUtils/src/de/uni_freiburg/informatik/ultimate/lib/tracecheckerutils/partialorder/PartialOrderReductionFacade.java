/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.CoveringMode;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDeadEndStore;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.MinimalSleepSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetCoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.CachedBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.ISleepMapStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.OptimisticBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMap;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * A facade to simplify interaction with Partial Order Reduction, specifically in the context of verification.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters occurring in the automata that will be reduced.
 * @param <H>
 *            The type of abstraction levels if abstract independence is used. Arbitrary type otherwise.
 */
public class PartialOrderReductionFacade<L extends IIcfgTransition<?>> {
	// Turn on to prune sleep set states where same program state with smaller sleep set already explored.
	public static final boolean ENABLE_COVERING_OPTIMIZATION = false;

	public enum OrderType {
		BY_SERIAL_NUMBER, PSEUDO_LOCKSTEP, RANDOM, POSITIONAL_RANDOM, LOOP_LOCKSTEP
	}

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;

	private final PartialOrderMode mMode;
	private final IDfsOrder<L, IPredicate> mDfsOrder;
	private final ISleepSetStateFactory<L, IPredicate, IPredicate> mSleepFactory;
	private final ISleepMapStateFactory<L, IPredicate, IPredicate> mSleepMapFactory;

	private StateSplitter<IPredicate> mStateSplitter;
	private final IDeadEndStore<IPredicate, IPredicate> mDeadEndStore;

	private final IIcfg<?> mIcfg;
	private final Collection<? extends IcfgLocation> mErrorLocs;

	private final List<IIndependenceRelation<IPredicate, L>> mIndependenceRelations;
	private IPersistentSetChoice<L, IPredicate> mPersistent;
	private IBudgetFunction<L, IPredicate> mBudget;

	public PartialOrderReductionFacade(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs, final PartialOrderMode mode,
			final OrderType orderType, final long randomOrderSeed,
			final List<IIndependenceRelation<IPredicate, L>> independenceRelations) {
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);

		mMode = mode;
		if (independenceRelations.isEmpty() && mMode != PartialOrderMode.NONE) {
			throw new IllegalArgumentException("Need at least one independence relation");
		}
		if (independenceRelations.size() > 1 && mMode != PartialOrderMode.SLEEP_NEW_STATES) {
			throw new IllegalArgumentException("This mode does not support multiple independence relations");
		}
		mIndependenceRelations = new ArrayList<>(independenceRelations);

		mSleepFactory = createSleepFactory(predicateFactory);
		mSleepMapFactory = createSleepMapFactory(predicateFactory);
		mDfsOrder = getDfsOrder(orderType, randomOrderSeed, icfg, errorLocs);
		mDeadEndStore = createDeadEndStore();

		mIcfg = icfg;
		mErrorLocs = errorLocs;

		mPersistent = createPersistentSets(mIcfg, mErrorLocs);
	}

	public void replaceIndependence(final int index, final IIndependenceRelation<IPredicate, L> independence) {
		assert 0 <= index && index < mIndependenceRelations.size() : "Unsupported index";
		final IIndependenceRelation<IPredicate, L> oldRelation = mIndependenceRelations.get(index);
		if (Objects.equals(independence, oldRelation)) {
			return;
		}
		// TODO save statistics!
		mIndependenceRelations.set(index, independence);
		mPersistent = createPersistentSets(mIcfg, mErrorLocs);
	}

	public IIndependenceRelation<IPredicate, L> getIndependence(final int index) {
		return mIndependenceRelations.get(index);
	}

	private ISleepSetStateFactory<L, IPredicate, IPredicate>
			createSleepFactory(final PredicateFactory predicateFactory) {
		if (!mMode.hasSleepSets()) {
			return null;
		}
		if (mIndependenceRelations.size() > 1) {
			// We need a sleep map factory instead, see #createSleepMapFactory
			return null;
		}
		if (mMode.doesUnrolling()) {
			final var factory = new SleepSetStateFactoryForRefinement<L>(predicateFactory);
			mStateSplitter = StateSplitter.extend(mStateSplitter, factory::getOriginalState, factory::getSleepSet);
			return factory;
		}
		return new ISleepSetStateFactory.NoUnrolling<>();
	}

	private ISleepMapStateFactory<L, IPredicate, IPredicate>
			createSleepMapFactory(final PredicateFactory predicateFactory) {
		if (mIndependenceRelations.size() <= 1) {
			return null;
		}
		final var factory = new SleepMapStateFactory<L>(predicateFactory);
		mStateSplitter = StateSplitter.extend(mStateSplitter, factory::getOriginalState,
				p -> new Pair<>(factory.getSleepMap(p), factory.getBudget(p)));
		return factory;
	}

	public ISleepSetStateFactory<L, IPredicate, IPredicate> getSleepFactory() {
		return mSleepFactory;
	}

	public ISleepMapStateFactory<L, IPredicate, IPredicate> getSleepMapFactory() {
		return mSleepMapFactory;
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
			final var order =
					new LoopLockstepOrder<L>(icfg, mStateSplitter == null ? null : mStateSplitter::getOriginal);
			mStateSplitter = StateSplitter.extend(mStateSplitter, x -> ((PredicateWithLastThread) x).getUnderlying(),
					x -> ((PredicateWithLastThread) x).getLastThread());
			return order;
		default:
			throw new UnsupportedOperationException("Unknown order type: " + orderType);
		}
	}

	private final IPersistentSetChoice<L, IPredicate> createPersistentSets(final IIcfg<?> icfg,
			final Collection<? extends IcfgLocation> errorLocs) {
		if (!mMode.hasPersistentSets()) {
			return null;
		}

		// TODO Persistent sets currently only supported for single independence relation
		final IIndependenceRelation<IPredicate, L> independence =
				IndependenceBuilder.fromIndependence(mIndependenceRelations.get(0)).ensureUnconditional().build();
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

	public void setBudget(final IBudgetFunction<L, IPredicate> budget) {
		mBudget = budget;
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
		if (mSleepFactory instanceof SleepSetStateFactoryForRefinement<?>) {
			((SleepSetStateFactoryForRefinement<?>) mSleepFactory).reset();
		}

		final IIndependenceRelation<IPredicate, L> independence =
				mIndependenceRelations.isEmpty() ? null : mIndependenceRelations.get(0);
		switch (mMode) {
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(mAutomataServices, input, mSleepFactory, independence, mDfsOrder, visitor);
			break;
		case SLEEP_NEW_STATES:
			if (mIndependenceRelations.size() == 1) {
				DepthFirstTraversal.traverse(mAutomataServices,
						new MinimalSleepSetReduction<>(input, mSleepFactory, independence, mDfsOrder), mDfsOrder,
						visitor);
			} else {
				final var red = new SleepMapReduction<>(input, mIndependenceRelations, mDfsOrder, mSleepMapFactory,
						new CachedBudget<>(mBudget));
				((OptimisticBudget<L, IPredicate, IPredicate, ?>) mBudget).setReduction(red);
				DepthFirstTraversal.traverse(mAutomataServices, red, mDfsOrder, visitor);
			}
			break;
		case PERSISTENT_SETS:
			PersistentSetReduction.applyWithoutSleepSets(mAutomataServices, input, mDfsOrder, mPersistent, visitor);
			break;
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
		case PERSISTENT_SLEEP_DELAY_SET:
			PersistentSetReduction.applyDelaySetReduction(mAutomataServices, input, independence, mDfsOrder,
					mPersistent, visitor);
			break;
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
		case PERSISTENT_SLEEP_NEW_STATES:
			PersistentSetReduction.applyNewStateReduction(mAutomataServices, input, independence, mDfsOrder,
					mSleepFactory, mPersistent, visitor);
			break;
		case NONE:
			DepthFirstTraversal.traverse(mAutomataServices, input, mDfsOrder, visitor);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);
		}
	}

	private IDeadEndStore<IPredicate, IPredicate> createDeadEndStore() {
		if (mStateSplitter == null) {
			return new IDeadEndStore.SimpleDeadEndStore<>();
		}
		return new IDeadEndStore.ProductDeadEndStore<>(mStateSplitter::getOriginal, mStateSplitter::getExtraInfo);
	}

	public IDeadEndStore<IPredicate, IPredicate> getDeadEndStore() {
		return mDeadEndStore;
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
		final AutomatonConstructingVisitor<L, IPredicate> visitor;
		if (mStateSplitter != null) {
			visitor = new AutomatonConstructingVisitor<>(x -> input.isInitial(mStateSplitter.getOriginal(x)),
					x -> input.isFinal(mStateSplitter.getOriginal(x)), input.getVpAlphabet(), mAutomataServices,
					emptyStackFactory);
		} else {
			visitor = new AutomatonConstructingVisitor<>(input, mAutomataServices, emptyStackFactory);
		}
		apply(input, visitor);
		return visitor.getReductionAutomaton();
	}

	public NestedWordAutomaton<L, IPredicate> constructReduction(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final Predicate<IPredicate> isAccepting) throws AutomataOperationCanceledException {
		final IDfsVisitor<L, IPredicate> buildVisitor = createBuildVisitor(abstraction.getVpAlphabet(), isAccepting);
		apply(abstraction, buildVisitor);
		AutomatonConstructingVisitor<L, IPredicate> builder;
		if (buildVisitor instanceof WrapperVisitor<?, ?, ?>) {
			builder = (AutomatonConstructingVisitor<L, IPredicate>) ((WrapperVisitor<L, IPredicate, ?>) buildVisitor)
					.getBaseVisitor();
		} else {
			builder = (AutomatonConstructingVisitor<L, IPredicate>) buildVisitor;
		}
		return builder.getReductionAutomaton();
	}

	private IDfsVisitor<L, IPredicate> createBuildVisitor(final VpAlphabet<L> alphabet,
			final Predicate<IPredicate> isAccepting) {
		IDfsVisitor<L, IPredicate> visitor = new AutomatonConstructingVisitor<>(x -> false, isAccepting, alphabet,
				new AutomataLibraryServices(mServices), mSleepFactory);

		if (getDfsOrder() instanceof BetterLockstepOrder<?, ?>) {
			visitor = ((BetterLockstepOrder<L, IPredicate>) getDfsOrder()).wrapVisitor(visitor);
		}

		if (ENABLE_COVERING_OPTIMIZATION) {
			visitor = new CoveringOptimizationVisitor<>(visitor, new SleepSetCoveringRelation<>(mSleepFactory),
					CoveringMode.PRUNE);
		}
		return new DeadEndOptimizingSearchVisitor<>(visitor, mDeadEndStore, true);
	}

	public void reportStatistics(final String pluginId) {
		for (int i = 0; i < mIndependenceRelations.size(); ++i) {
			final StatisticsData data = new StatisticsData();
			data.aggregateBenchmarkData(mIndependenceRelations.get(i).getStatistics());
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Independence relation #" + (i + 1) + " benchmarks", data));
		}

		if (mPersistent != null) {
			final StatisticsData persistentData = new StatisticsData();
			persistentData.aggregateBenchmarkData(mPersistent.getStatistics());
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Persistent set benchmarks", persistentData));
		}
	}

	public StateSplitter<IPredicate> getStateSplitter() {
		return mStateSplitter;
	}

	private static class SleepMapStateFactory<L> implements ISleepMapStateFactory<L, IPredicate, IPredicate> {

		private final IPredicate mEmptyStack;

		private final NestedMap3<IPredicate, SleepMap<L, IPredicate>, Integer, SleepMapPredicate<L>> mMap =
				new NestedMap3<>();

		public SleepMapStateFactory(final PredicateFactory predicateFactory) {
			mEmptyStack = predicateFactory.newEmptyStackPredicate();
		}

		@Override
		public IPredicate createEmptyStackState() {
			return mEmptyStack;
		}

		@Override
		public IPredicate createSleepMapState(final IPredicate state, final SleepMap<L, IPredicate> sleepMap,
				final int budget) {
			final SleepMapPredicate<L> existing = mMap.get(state, sleepMap, budget);
			if (existing != null) {
				return existing;
			}

			final SleepMapPredicate<L> predicate = new SleepMapPredicate<>((IMLPredicate) state, sleepMap, budget);
			mMap.put(state, sleepMap, budget, predicate);
			return predicate;
		}

		@Override
		public IPredicate getOriginalState(final IPredicate sleepMapState) {
			return ((SleepMapPredicate<?>) sleepMapState).getUnderlying();
		}

		@Override
		public SleepMap<L, IPredicate> getSleepMap(final IPredicate sleepMapState) {
			return ((SleepMapPredicate<L>) sleepMapState).getSleepMap();
		}

		@Override
		public int getBudget(final IPredicate sleepMapState) {
			return ((SleepMapPredicate<?>) sleepMapState).getBudget();
		}

	}

	public static class SleepMapPredicate<L> implements IMLPredicate {
		private final IMLPredicate mUnderlying;
		private final SleepMap<L, IPredicate> mSleepMap;
		private final int mBudget;

		public SleepMapPredicate(final IMLPredicate underlying, final SleepMap<L, IPredicate> sleepMap,
				final int budget) {
			mUnderlying = underlying;
			mSleepMap = sleepMap;
			mBudget = budget;
		}

		@Override
		public Term getFormula() {
			return mUnderlying.getFormula();
		}

		@Override
		public Term getClosedFormula() {
			return mUnderlying.getClosedFormula();
		}

		@Override
		public String[] getProcedures() {
			return mUnderlying.getProcedures();
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mUnderlying.getVars();
		}

		@Override
		public IcfgLocation[] getProgramPoints() {
			return mUnderlying.getProgramPoints();
		}

		public IMLPredicate getUnderlying() {
			return mUnderlying;
		}

		public SleepMap<L, IPredicate> getSleepMap() {
			return mSleepMap;
		}

		public int getBudget() {
			return mBudget;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mBudget, mSleepMap, mUnderlying);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SleepMapPredicate<?> other = (SleepMapPredicate<?>) obj;
			return mBudget == other.mBudget && Objects.equals(mSleepMap, other.mSleepMap)
					&& Objects.equals(mUnderlying, other.mUnderlying);
		}

		@Override
		public String toString() {
			return "SleepMapPredicate [underlying: " + mUnderlying + ", budget: " + mBudget + ", map: " + mSleepMap
					+ "]";
		}
	}

	/**
	 * Helper class to split states of reduction automata into the original state (i.e., the state of the input
	 * automaton) and extra information added by reduction algorithms.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 */
	public static class StateSplitter<S> {
		private final Function<S, S> mGetOriginal;
		private final Function<S, Object> mGetExtraInfo;

		public StateSplitter(final Function<S, S> getOriginal, final Function<S, Object> getExtraInfo) {
			mGetOriginal = Objects.requireNonNull(getOriginal);
			mGetExtraInfo = Objects.requireNonNull(getExtraInfo);
		}

		public S getOriginal(final S t) {
			return mGetOriginal.apply(t);
		}

		Object getExtraInfo(final S t) {
			return mGetExtraInfo.apply(t);
		}

		static <T> StateSplitter<T> extend(final StateSplitter<T> first, final Function<T, T> newGetOriginal,
				final Function<T, Object> newGetExtraInfo) {
			assert newGetOriginal != null;
			assert newGetExtraInfo != null;
			if (first == null) {
				return new StateSplitter<>(newGetOriginal, newGetExtraInfo);
			}
			return new StateSplitter<>(first.mGetOriginal.andThen(newGetOriginal),
					addExtraInfo(first.mGetOriginal, first.mGetExtraInfo, newGetExtraInfo));
		}

		private static <T> Function<T, Object> addExtraInfo(final Function<T, T> oldGetOriginal,
				final Function<T, Object> oldGetInfo, final Function<T, Object> newGetInfo) {
			return x -> new Pair<>(oldGetInfo.apply(x), newGetInfo.apply(oldGetOriginal.apply(x)));
		}
	}
}
