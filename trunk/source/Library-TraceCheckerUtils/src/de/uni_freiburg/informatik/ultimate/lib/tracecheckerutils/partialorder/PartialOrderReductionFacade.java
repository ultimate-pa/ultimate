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

import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.MonitorProduct;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConditionTransformingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDeadEndStore;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.MinimalSleepSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMonitorStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
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
	private StateSplitter<IPredicate> mStateSplitter;
	private final IDeadEndStore<IPredicate, IPredicate> mDeadEndStore;
	private final IPreferenceOrder<L, IPredicate, ?> mPreferenceOrder;

	public PartialOrderReductionFacade(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs, final PartialOrderMode mode,
			final OrderType orderType, final long randomOrderSeed,
			final IIndependenceRelation<IPredicate, L> independence) {
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mMode = mode;
		mSleepFactory = createSleepFactory(predicateFactory);
		mPreferenceOrder = getPreferenceOrder(icfg);
		mDfsOrder = getDfsOrder(orderType, randomOrderSeed, icfg, errorLocs);
		mIndependence = independence;
		mPersistent = createPersistentSets(icfg, errorLocs);
		mDeadEndStore = createDeadEndStore();
	}

	private IPreferenceOrder<L, IPredicate, ?> getPreferenceOrder(final IIcfg<?> icfg) {

		final List<String> threadList =
				IcfgUtils.getAllThreadInstances(icfg).stream().sorted().collect(Collectors.toList());
		final VpAlphabet<L> alphabet = Cfg2Automaton.extractVpAlphabet(icfg, true);
		return new ParameterizedPreferenceOrder(1, threadList, alphabet, x -> true);
	}

	private ISleepSetStateFactory<L, IPredicate, IPredicate>
			createSleepFactory(final PredicateFactory predicateFactory) {
		if (!mMode.hasSleepSets()) {
			return null;
		}
		if (mMode.doesUnrolling()) {
			final var factory = new SleepSetStateFactoryForRefinement<L>(predicateFactory);
			mStateSplitter = StateSplitter.extend(mStateSplitter, factory::getOriginalState, factory::getSleepSet);
			return factory;
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
		// TODO handle preference orders with monitor automata

		if (mMode.hasFixedOrder() && mDfsOrder instanceof LoopLockstepOrder<?>) {
			// For stateful orders, we need to include the chosen order in the normalization if we want to guarantee
			// compatibility of persistent sets.
			return new Pair<>(((IMLPredicate) state).getProgramPoints(), mDfsOrder.getOrder(state));
		}
		return ((IMLPredicate) state).getProgramPoints();
	}

	public IDfsOrder<L, IPredicate> getDfsOrder() {
		return mDfsOrder;
	}

	/**
	 * An interface used to create a visitor.
	 *
	 * We need this indirection so callers need not be aware of the intricate internal structure of states in the
	 * reduction automaton to which the visitor is applied (monitor states, sleep sets, etc.). Instead, the only
	 * information given is how the underlying's input automaton state can be extracted from a state of the reduction
	 * automaton.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters
	 * @param <S>
	 *            The type of states in the input automaton
	 */
	@FunctionalInterface
	interface IVisitorProvider<L, S> {
		/**
		 * Provides the visitor.
		 *
		 * @param <R>
		 *            The type of states in the reduction automaton
		 * @param originalState
		 *            A function that extracts the original state from a state of the reduction automaton, which can be
		 *            used to construct the visitor.
		 * @return the visitor
		 */
		<R> IDfsVisitor<L, R> getVisitor(Function<R, S> originalState);
	}

	/**
	 * Apply POR to a given automaton.
	 *
	 * @param input
	 *            The automaton to which reduction is applied
	 * @param visitorProvider
	 *            Provides a visitor that traverses the reduced automaton
	 *
	 * @throws AutomataLibraryException
	 *             if some automata operation fails
	 * @throws AutomataOperationCanceledException
	 *             if the traversal encounters a timeout
	 */
	// TODO problem: caller needs access to visitor result
	public void apply(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IVisitorProvider<L, IPredicate> visitorProvider) throws AutomataLibraryException {
		applyWithMonitor(input, visitorProvider, mPreferenceOrder, Function.identity());
	}

	// If the current preference order has a monitor, take the product of the input and the monitor.
	// Then call #applyReduction.
	private <R, M> void applyWithMonitor(final INwaOutgoingLetterAndTransitionProvider<L, R> input,
			final IVisitorProvider<L, IPredicate> visitorProvider, final IPreferenceOrder<L, R, M> preference,
			final Function<R, IPredicate> getOriginal) throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<L, M> monitor = preference.getMonitor();
		if (monitor != null) {
			final var product = new MonitorProduct<>(input, monitor, new IMonitorStateFactory.Default<>());
			final IDfsOrder<L, Pair<R, M>> order = new Preference2DfsOrder<>(preference, Function.identity());
			applyReduction(product, visitorProvider, order, getOriginal.compose(Pair::getFirst));
		} else {
			final IDfsOrder<L, R> order = new Preference2DfsOrder<>(preference, x -> new Pair<>(x, null));
			applyReduction(input, visitorProvider, order, getOriginal);
		}
	}

	// Applies sleep set and/or persistent set reduction
	private <R> void applyReduction(final INwaOutgoingLetterAndTransitionProvider<L, R> input,
			final IVisitorProvider<L, IPredicate> visitorProvider, final IDfsOrder<L, R> order,
			final Function<R, IPredicate> getOriginal) throws AutomataOperationCanceledException {
		switch (mMode) {
		// DFS-based modes
		case SLEEP_NEW_STATES:
			applyDfs(
					new MinimalSleepSetReduction<>(input, new ISleepSetStateFactory.MinimalReduction<>(),
							lift(mIndependence, getOriginal), lift(order)),
					visitorProvider, lift(order), getOriginal.compose(Pair::getFirst));
			break;
		case PERSISTENT_SLEEP_NEW_STATES:
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
			final var extract = getOriginal.compose(Pair<R, ImmutableSet<L>>::getFirst);
			PersistentSetReduction.<L, R, Pair<R, ImmutableSet<L>>> applyNewStateReduction(mAutomataServices, input,
					lift(mIndependence, getOriginal), lift(order), new ISleepSetStateFactory.MinimalReduction<L, R>(),
					lift(mPersistent, extract), visitorProvider.getVisitor(extract));
			break;
		case PERSISTENT_SETS:
			PersistentSetReduction.applyWithoutSleepSets(mAutomataServices, input, order,
					lift(mPersistent, getOriginal), visitorProvider.getVisitor(getOriginal));
			break;
		case NONE:
			applyDfs(input, visitorProvider, order, getOriginal);
			break;

		// legacy modes (delay sets)
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(mAutomataServices, input, new ISleepSetStateFactory.NoUnrolling<>(),
					lift(mIndependence, getOriginal), order, visitorProvider.getVisitor(getOriginal));
			break;
		case PERSISTENT_SLEEP_DELAY_SET:
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
			PersistentSetReduction.applyDelaySetReduction(mAutomataServices, input, lift(mIndependence, getOriginal),
					order, lift(mPersistent, getOriginal), visitorProvider.getVisitor(getOriginal));
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mMode);
		}
	}

	// Performs the actual depth-first traversal (for persistent sets, this is already handled above).
	private <R, S> void applyDfs(final INwaOutgoingLetterAndTransitionProvider<L, R> input,
			final IVisitorProvider<L, S> visitorProvider, final IDfsOrder<L, R> order, final Function<R, S> getOriginal)
			throws AutomataOperationCanceledException {
		final var visitor = visitorProvider.getVisitor(getOriginal);
		new DepthFirstTraversal<>(mAutomataServices, input, order, visitor);
	}

	private <R, X> IDfsOrder<L, Pair<R, X>> lift(final IDfsOrder<L, R> order) {
		return new IDfsOrder<>() {
			@Override
			public Comparator<L> getOrder(final Pair<R, X> state) {
				return order.getOrder(state.getFirst());
			}

			@Override
			public boolean isPositional() {
				return order.isPositional();
			}
		};
	}

	private <R, S> IIndependenceRelation<R, L> lift(final IIndependenceRelation<S, L> indep,
			final Function<R, S> getOriginal) {
		return new ConditionTransformingIndependenceRelation<>(indep, getOriginal);
	}

	private <R, S> IPersistentSetChoice<L, R> lift(final IPersistentSetChoice<L, S> persistent,
			final Function<R, S> getOriginal) {
		return new IPersistentSetChoice<>() {
			@Override
			public Set<L> persistentSet(final R state) {
				return persistent.persistentSet(getOriginal.apply(state));
			}

			@Override
			public IStatisticsDataProvider getStatistics() {
				return persistent.getStatistics();
			}

			@Override
			public boolean ensuresCompatibility(final IDfsOrder<L, R> order) {
				return false; // TODO persistent.ensuresCompatibility(order);
			}
		};
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
	@Deprecated
	public void apply(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input,
			final IDfsVisitor<L, IPredicate> visitor) throws AutomataOperationCanceledException {
		if (mDfsOrder instanceof LoopLockstepOrder<?>) {
			input = ((LoopLockstepOrder<L>) mDfsOrder).wrapAutomaton(input);
		} else if (mPreferenceOrder.getMonitor() != null) {
			try {
				input = (new MonitorProduct(input, mPreferenceOrder.getMonitor(),
						new IMonitorStateFactory<Object, Object, Object>() {

							@Override
							public Object createEmptyStackState() {
								// TODO Auto-generated method stub
								return null;
							}

							@Override
							public Object product(final Object state1, final Object state2) {
								// TODO Auto-generated method stub

								return new MonitorPredicate((IMLPredicate) state1, state2);
							}
						}));
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException(e);
			}
		}
		if (mSleepFactory instanceof SleepSetStateFactoryForRefinement<?>) {
			((SleepSetStateFactoryForRefinement<?>) mSleepFactory).reset();
		}

		switch (mMode) {
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(mAutomataServices, input, mSleepFactory, mIndependence, mDfsOrder, visitor);
			break;
		case SLEEP_NEW_STATES:
			final var dfsorder = new Preference2DfsOrder(mPreferenceOrder, x -> {
				final var y = (MonitorPredicate) mStateSplitter.getOriginal((IPredicate) x);
				return new Pair<>(y.getState1(), y.getState2());
			});
			new DepthFirstTraversal<>(mAutomataServices,
					new MinimalSleepSetReduction<>(input, mSleepFactory, mIndependence, dfsorder), mDfsOrder, visitor);
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

	public void reportStatistics(final String pluginId) {
		final StatisticsData data = new StatisticsData();
		data.aggregateBenchmarkData(mIndependence.getStatistics());
		mServices.getResultService().reportResult(pluginId,
				new StatisticsResult<>(pluginId, "Independence relation benchmarks", data));

		if (mPersistent != null) {
			final StatisticsData persistentData = new StatisticsData();
			persistentData.aggregateBenchmarkData(mPersistent.getStatistics());
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Persistent set benchmarks", persistentData));
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
	private static class StateSplitter<S> {
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

	@Deprecated
	public static class MonitorPredicate implements IMLPredicate {

		private final IMLPredicate mState1;
		private final Object mState2;

		public MonitorPredicate(final IMLPredicate state1, final Object state2) {
			mState1 = state1;
			mState2 = state2;
		}

		@Override
		public Term getFormula() {
			return mState1.getFormula();
		}

		@Override
		public Term getClosedFormula() {
			// TODO Auto-generated method stub
			return mState1.getClosedFormula();
		}

		@Override
		public String[] getProcedures() {
			// TODO Auto-generated method stub
			return mState1.getProcedures();
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mState1.getVars();
		}

		@Override
		public IcfgLocation[] getProgramPoints() {
			return mState1.getProgramPoints();
		}

		public IMLPredicate getState1() {
			return mState1;
		}

		public Object getState2() {
			return mState2;
		}

	}
}
