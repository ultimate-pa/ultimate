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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
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
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
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
 * @param <H>
 *            The type of abstraction levels if abstract independence is used. Arbitrary type otherwise.
 */
public class PartialOrderReductionFacade<L extends IIcfgTransition<?>> {
	// Turn on to prune sleep set states where same program state with smaller sleep set already explored.
	public static final boolean ENABLE_COVERING_OPTIMIZATION = false;

	public enum OrderType {
		BY_SERIAL_NUMBER, PSEUDO_LOCKSTEP, RANDOM, POSITIONAL_RANDOM, LOOP_LOCKSTEP
	}

	public enum StepType {
		ALL_READ_WRITE, ALL_WRITE, GLOBAL_READ_WRITE, GLOBAL_WRITE, LOOP
	}

	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;

	private final PartialOrderMode mMode;
	private IDfsOrder<L, IPredicate> mDfsOrder;
	private final ISleepSetStateFactory<L, IPredicate, IPredicate> mSleepFactory;
	private final ISleepMapStateFactory<L, IPredicate, IPredicate> mSleepMapFactory;

	private StateSplitter<IPredicate> mStateSplitter;
	private final IDeadEndStore<?, IPredicate> mDeadEndStore;
	private final IPreferenceOrder<L, IPredicate, ?> mPreferenceOrder;

	private final IIcfg<?> mIcfg;
	private final Collection<? extends IcfgLocation> mErrorLocs;

	private final List<IIndependenceRelation<IPredicate, L>> mIndependenceRelations;
	private IPersistentSetChoice<L, IPredicate> mPersistent;
	private final Function<SleepMapReduction<L, IPredicate, IPredicate>, IBudgetFunction<L, IPredicate>> mGetBudget;

	private final List<StatisticsData> mOldIndependenceStatistics = new ArrayList<>();
	private final List<StatisticsData> mOldPersistentSetStatistics = new ArrayList<>();

	public PartialOrderReductionFacade(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs, final PartialOrderMode mode,
			final OrderType orderType, final long randomOrderSeed, final StepType steptype, final String threads,
			final int maxStep, final List<IIndependenceRelation<IPredicate, L>> independenceRelations,
			final Function<SleepMapReduction<L, IPredicate, IPredicate>, IBudgetFunction<L, IPredicate>> getBudget,
			final Function<StateSplitter<IPredicate>, IDeadEndStore<?, IPredicate>> getDeadEndStore) {
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
		mGetBudget = getBudget;

		mSleepFactory = createSleepFactory(predicateFactory);
		mSleepMapFactory = createSleepMapFactory(predicateFactory);
		mPreferenceOrder = getPreferenceOrder(steptype, threads, maxStep, icfg);
		// mDfsOrder = getDfsOrder(orderType, randomOrderSeed, icfg, errorLocs);

		// TODO decouple dead end support from this class
		mDeadEndStore = getDeadEndStore == null ? null : getDeadEndStore.apply(mStateSplitter);

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

		final StatisticsData indepData = new StatisticsData();
		indepData.aggregateBenchmarkData(oldRelation.getStatistics());
		mOldIndependenceStatistics.add(indepData);

		if (mPersistent != null) {
			final StatisticsData persData = new StatisticsData();
			persData.aggregateBenchmarkData(mPersistent.getStatistics());
			mOldPersistentSetStatistics.add(persData);
		}

		mIndependenceRelations.set(index, independence);
		mPersistent = createPersistentSets(mIcfg, mErrorLocs);
	}

	public IIndependenceRelation<IPredicate, L> getIndependence(final int index) {
		return mIndependenceRelations.get(index);
	}

	private IPreferenceOrder<L, IPredicate, ?> getPreferenceOrder(final StepType steptype, final String threads,
			final int maxStep, final IIcfg<?> icfg) {
		// TODO Add support for all orders previously supported in #getDfsOrder

		//TODO heuristic


		final List<String> allThreads = new ArrayList<>();
		allThreads.addAll(IcfgUtils.getAllThreadInstances(icfg).stream().sorted().collect(Collectors.toList()));
		final String start = "ULTIMATE.start";
		for (int i = allThreads.indexOf(start); i > 0; i--) {
			allThreads.set(i, allThreads.get(i - 1));
		}
		allThreads.set(0, start);
		final String[] pairList = threads.split("\\s+");

		List<Integer> maxSteps = new ArrayList<>();
		final List<String> threadList = new ArrayList<>();
		if (pairList[0].equals("X")) {
			threadList.addAll(allThreads);
			maxSteps = Collections.nCopies(threadList.size(), maxStep);
		} else {
			final List<Boolean> allThreadsBool = new ArrayList<>();
			allThreadsBool.addAll(Collections.nCopies(allThreads.size(), false));
			for (final String pair : pairList) {
				final String[] splittedPair = pair.split(",");
				final Integer index = Integer.parseInt(splittedPair[0]);
				if (allThreads.size() > index) {
					threadList.add(allThreads.get(index));
					maxSteps.add(Integer.parseInt(splittedPair[1]));
					if (!allThreadsBool.get(index)) {
						allThreadsBool.set(index, true);
					}
				}
			}
			for (int i = 0; i < allThreadsBool.size(); i++) {
				if (!allThreadsBool.get(i)) {
					threadList.add(allThreads.get(i));
					maxSteps.add(1);
				}
			}
		}
		final VpAlphabet<L> alphabet = Cfg2Automaton.extractVpAlphabet(icfg, true);

		/* TODO get all global Variables, then iterate over the cfg and mark variables if a procedure accesses it,
		* remove all variables that are marked at most once at the end to calculate the effective global variables
		* can also be done via the heuristic
		*/
		
		final IPreferenceOrder<L, IPredicate, ?> order =
				new ParameterizedPreferenceOrder<>(maxSteps, threadList, alphabet, getStepDefinition(icfg, steptype));

		if (order.getMonitor() != null) {
			final var splitter = mStateSplitter;
			mDfsOrder = new Preference2DfsOrder<>(order, x -> {
				final var y = (MonitorPredicate) splitter.getOriginal(x);
				return new Pair(y.getUnderlying(), y.getMonitorState());
			});
			mStateSplitter = StateSplitter.extend(mStateSplitter, x -> ((MonitorPredicate) x).getUnderlying(),
					x -> ((MonitorPredicate) x).getMonitorState());
		}

		return order;
	}

	private Predicate<L> getStepDefinition(final IIcfg<?> icfg, final StepType steptype
			/*, final Set<IProgramVar> effectiveGlobalVars*/) {

		switch (steptype) {
		case ALL_READ_WRITE:
			return x -> (!x.getTransformula().getInVars().isEmpty()
					|| !x.getTransformula().getAssignedVars().isEmpty());
		case ALL_WRITE:
			return x -> !x.getTransformula().getAssignedVars().isEmpty();
		case GLOBAL_READ_WRITE:
			return x -> x.getTransformula().getInVars().keySet().stream().anyMatch(v -> v.isGlobal())
					|| x.getTransformula().getAssignedVars().stream().anyMatch(v -> v.isGlobal());
			// v.isGlobal() should be modified s.t. it has to be "effectively global"
		case GLOBAL_WRITE:
			return x -> x.getTransformula().getAssignedVars().stream().anyMatch(v -> v.isGlobal());
			// v.isGlobal() should be modified s.t. it has to be "effectively global"
		case LOOP:
			final var loopHeads = icfg.getLoopLocations();
			return x -> loopHeads.contains(x.getTarget());
		}
		throw new UnsupportedOperationException("Unknown step type: " + steptype);
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
							.thenComparing(Comparator.comparing(x -> x.getPrecedingProcedure()))
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
		assert mIndependenceRelations.size() == 1; // TODO
		final IIndependenceRelation<IPredicate, L> independence = mIndependenceRelations.get(0);

		switch (mMode) {
		// DFS-based modes
		case SLEEP_NEW_STATES:
			applyDfs(
					new MinimalSleepSetReduction<>(input, new ISleepSetStateFactory.MinimalReduction<>(),
							lift(independence, getOriginal), lift(order)),
					visitorProvider, lift(order), getOriginal.compose(Pair::getFirst));
			break;
		case PERSISTENT_SLEEP_NEW_STATES:
		case PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER:
			final var extract = getOriginal.compose(Pair<R, ImmutableSet<L>>::getFirst);
			PersistentSetReduction.<L, R, Pair<R, ImmutableSet<L>>> applyNewStateReduction(mAutomataServices, input,
					lift(independence, getOriginal), lift(order), new ISleepSetStateFactory.MinimalReduction<L, R>(),
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
					lift(independence, getOriginal), order, visitorProvider.getVisitor(getOriginal));
			break;
		case PERSISTENT_SLEEP_DELAY_SET:
		case PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER:
			PersistentSetReduction.applyDelaySetReduction(mAutomataServices, input, lift(independence, getOriginal),
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
		DepthFirstTraversal.traverse(mAutomataServices, input, order, visitor);
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
						mGetBudget.andThen(CachedBudget::new));
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
		int i = 0;
		for (final StatisticsData data : mOldIndependenceStatistics) {
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Independence relation #" + (i + 1) + " benchmarks", data));
			i++;
		}

		for (final var relation : mIndependenceRelations) {
			final StatisticsData data = new StatisticsData();
			data.aggregateBenchmarkData(relation.getStatistics());
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Independence relation #" + (i + 1) + " benchmarks", data));
			i++;
		}

		for (final StatisticsData data : mOldPersistentSetStatistics) {
			mServices.getResultService().reportResult(pluginId,
					new StatisticsResult<>(pluginId, "Persistent set benchmarks", data));
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

		public Object getExtraInfo(final S t) {
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
	public static class MonitorPredicate<M> extends AnnotatedMLPredicate<M> {
		public MonitorPredicate(final IMLPredicate state, final M monitorState) {
			super(state, monitorState);
		}

		public M getMonitorState() {
			return mAnnotation;
		}
	}
}
