//package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;
//
//import java.util.ArrayList;
//import java.util.Collection;
//import java.util.Collections;
//import java.util.HashMap;
//import java.util.HashSet;
//import java.util.List;
//import java.util.Map;
//import java.util.Set;
//import java.util.stream.Collectors;
//
//import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
//import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
//import de.uni_freiburg.informatik.ultimate.logic.Script;
//import de.uni_freiburg.informatik.ultimate.logic.Term;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;
//import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
//
//public class GuardedInterferenceDomainPostOperatorBACKUP<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
//		implements IAbstractPostOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> {
//	private String mCurrentThreadName;
//
//	private final ILogger mLogger;
//
//	private AbstractInterferenceState<STATE, ACTION> mInterferences;
//	private AbstractInterferenceState<STATE, ACTION> mNewInterferences;
//	private final CfgSmtToolkit mToolkit;
//	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
//	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
//	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
//	private final Set<IProgramNonOldVar> mGlobalVariables;
//	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, STATE> mInterferenceCache = new HashMap<>();
//	private final AbstractLocationMap<LOC> mAbstractLocationMap;
//
//	private final int MAXITF = 1;
//	private final int MAXSIZE = 10;
//	private int mIterations;
//	private boolean mForked = false;
//
//	public GuardedInterferenceDomainPostOperatorBACKUP(final IIcfg<?> cfg, final ILogger logger,
//			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
//			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
//			final AbstractInterferenceState<STATE, ACTION> interferenceState,
//			final AbstractLocationMap<LOC> locationMap) {
//		mLogger = logger;
//		mToolkit = cfg.getCfgSmtToolkit();
//		mUnderlyingDomain = underlying;
//		mUnderlyingPostOp = postOp;
//		mGuardedInterferenceDomain = relationalInterferingDomain;
//		mGlobalVariables = mToolkit.getSymbolTable().getGlobals();
//		mInterferences = interferenceState;
//		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
//		mAbstractLocationMap = locationMap;
//	}
//
//	public AbstractInterferenceState<STATE, ACTION> getInterferences() {
//		return mInterferences;
//	}
//
//	public void setInterferences(final AbstractInterferenceState<STATE, ACTION> newState) {
//		mInterferences = newState;
//	}
//
//	public void updateInterferences() {
//		mInterferences = new AbstractInterferenceState<>(mNewInterferences);
//		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());
//	}
//
//	@Override
//	public Collection<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> apply(
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final ACTION transition) {
//		if (oldstate.isBottom()) {
//			return List.of(oldstate);
//		}
//		mCurrentThreadName = transition.getPrecedingProcedure();
//
//		// handle fork differently
//		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
//			return applyFork(oldstate, transition);
//		}
//
//		// 1. normal poststate
//		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postRelationalState = new GuardedInterferenceDomainStateDisj<>(
//				mUnderlyingDomain, MAXSIZE,
//				oldstate.getStates().stream()
//						.flatMap(s -> mUnderlyingPostOp.apply(s.state(), transition).stream().filter(a -> !a.isBottom())
//								.map(newState -> new GuardedInterferenceDomainState<>(newState, s.threadCounter(),
//										s.abstractLocationState().copyToNewState(transition.getTarget()))))
//						.collect(Collectors.toSet()));
//
////		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postRelationalState = new GuardedInterferenceDomainStateDisj<>(
////				mUnderlyingDomain, mUnderlyingPostOp.apply(oldstate.getUnderlyingState(), transition),
////				oldstate.getThreadInstanceState(),
////				oldstate.getAbstractLocationState().copyToNewState(transition.getTarget()));
//		mLogger.info("post(" + oldstate.toLogString() + ", " + transition + ") = " + postRelationalState);
////		mLogger.info(postRelationalState.getAbstractLocationState());
//
//		// 2. Add new interference to global map
//		if (isInterferingTransition(transition)) {
//			// TODO: we are abstracting here, maybe reconsider for more precision
//			final var singleAbstractState = oldstate.getSingleState();
//			mNewInterferences.addInterference(mCurrentThreadName, transition, singleAbstractState.state(),
//					singleAbstractState.threadCounter());
//		}
//
//		// 3. apply interferences
//		postRelationalState = stateAfterInterferences(postRelationalState, mCurrentThreadName);
////		postRelationalState = new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE,
////				Set.of(postRelationalState.getSingleState()));
//
//		return List.of(postRelationalState);
//	}
//
//	private boolean isInterferingTransition(final ACTION transition) {
//		// abstract locations kind of force us to make everything an interference, otherwise we don't move on in
//		// abstractlocation trackers of other threads -> stuck, unsound
//		return true;
//		// if (!transition.getTransformula().getAssignedVars().stream()
//		// .anyMatch(assignedVar -> mGlobalVariables.contains(assignedVar))) {
//		// return false;
//		// }
//		// if (!(transition instanceof final StatementSequence statementSequence)) {
//		// return true;
//		// }
//		// for (final Statement statement : statementSequence.getStatements()) {
//		// if (!(statement instanceof AssumeStatement)) {
//		// return true;
//		// }
//		// }
//		// return false;
//	}
//
//	private Collection<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> applyFork(
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final ACTION transition) {
//
//		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState = new GuardedInterferenceDomainStateDisj<>(
//				mUnderlyingDomain, MAXSIZE,
//				oldstate.getStates().stream()
//						.map(s -> new GuardedInterferenceDomainState<>(s.state(), s.threadCounter(),
//								s.abstractLocationState().copyToNewState(transition.getTarget())))
//						.collect(Collectors.toSet()));
//
////		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState = new GuardedInterferenceDomainStateDisj<>(
////				mUnderlyingDomain, oldstate.getUnderlyingState(), oldstate.getThreadInstanceState(),
////				oldstate.getAbstractLocationState().copyToNewState(transition.getTarget()));
//
//		if (transition instanceof final ForkThreadCurrent fork1) {
//			final boolean circular = isCircular(fork1, fork1.getSource().getIncomingEdges(), 0);
//			final var forked = fork1.getNameOfForkedProcedure();
//			newState = newState.incrementThread(forked);
//			final Set<GuardedInterferenceDomainState<STATE, LOC>> updatedStates = new HashSet<>();
//			for (final GuardedInterferenceDomainState<STATE, LOC> singleState : newState.getStates()) {
//				if (circular || singleState.threadCounter().getThreadInstances().get(forked) > 0) {
//					updatedStates.add(singleState.setThreadsInf(List.of(forked)));
//				} else {
//					updatedStates.add(singleState);
//				}
//			}
//			newState = new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE, updatedStates);
//		} else {
//			throw new IllegalArgumentException("Unsupported fork transition type");
//		}
//		// apply interferences
//		newState = stateAfterInterferences(newState, mCurrentThreadName);
//
//		final var singleAbstractState = oldstate.getSingleState();
//		mNewInterferences.addForkInterference(mCurrentThreadName, transition, singleAbstractState.state(),
//				singleAbstractState.threadCounter());
//		return List.of(newState);
//	}
//
//	public boolean isCircular(final IcfgEdge fork1, final List<IcfgEdge> edges, final int depth) {
//		// TODO: replace by caching all statements seen, breaking when any seen again
//		if (depth > 100) {
//			return false;
//		}
//		if (edges.isEmpty()) {
//			return false;
//		}
//		if (edges.contains(fork1)) {
//			return true;
//		}
//		for (final IcfgEdge icfgEdge : edges) {
//			if (isCircular(fork1, icfgEdge.getSource().getIncomingEdges(), depth + 1)) {
//				return true;
//			}
//		}
//		return false;
//	}
//
//	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> stateAfterInterferences(
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final String ownerThread) {
//
//		// this check might cost more time than it saves, if we don't encounter a lot of top-states
//		final var topstate = mUnderlyingDomain.createTopState();
//		final var diff = DataStructureUtils.difference(oldstate.getVariables(), topstate.getVariables());
//		final var topWithVars = topstate.addVariables(diff);
//
//		// get a single underlying state from oldstate, but do not rely on a singleState approach
//		// instead we check if top covers all of them. if it does, no interferences needed
//		boolean coveredAll = true;
//		for (final GuardedInterferenceDomainState<STATE, LOC> single : oldstate.getStates()) {
//			if (topWithVars.isSubsetOf(single.state()) == SubsetResult.NONE) {
//				coveredAll = false;
//				break;
//			}
//		}
//		if (coveredAll) {
//			return oldstate;
//		}
//
//		// compute which threads can interfere in this state
//		final Set<String> threadNameSet = new HashSet<>();
//		final Map<String, Integer> maxInstances = new HashMap<>();
//		for (final GuardedInterferenceDomainState<STATE, LOC> single : oldstate.getStates()) {
//			threadNameSet.addAll(single.threadCounter().getThreadNameSet());
//			single.threadCounter().getThreadInstances().forEach((k, v) -> maxInstances.merge(k, v, Math::max));
//		}
//		final Set<String> possibleInterferenceSet = new HashSet<>();
//		for (final String thread : threadNameSet) {
//			final int threadInstances = maxInstances.getOrDefault(thread, 0);
//			if (threadInstances >= 2 || (!thread.equals(ownerThread) && threadInstances > 0)) {
//				possibleInterferenceSet.add(thread);
//			}
//		}
//
//		return oldstate.union(interferenceFixpoint(possibleInterferenceSet, oldstate, ownerThread));
//	}
//
//	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> interferenceFixpoint(
//			final Set<String> interferingThreads, final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> state,
//			final String ownerThread) {
//		mIterations = 0;
//		var newState = state;
//		mForked = false;
//		while (true) {
//			mIterations++;
//			// state just to check if fixpoint reached
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> beginLoopState = newState;
//			for (final String interferenceThreadName : interferingThreads) {
//				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
//				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
//					continue;
//				}
//				newState = newState
//						.union(applyInterferences(newState, interferences, ownerThread, interferenceThreadName));
//			}
//			final boolean changed = newState.isSubsetOf(beginLoopState) == SubsetResult.NONE;
//			if (!changed) {
//				break;
//			}
//		}
//		if (mForked) {
//			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
//			return newState.union(stateAfterInterferences(newState, ownerThread));
//		}
//		return newState;
//	}
//
//	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
//			Interference<STATE, ACTION> interf, STATE targetState) {
//	}
//
//	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> applyInterferences(
//			GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> current,
//			final Set<Interference<STATE, ACTION>> interferences, final String ownerThread,
//			final String interferenceThreadName) {
//		for (final Interference<STATE, ACTION> interference : interferences) {
//			final Set<GuardedInterferenceDomainState<STATE, LOC>> updatedStates = new HashSet<>();
//
//			for (final GuardedInterferenceDomainState<STATE, LOC> singleState : current.getStates()) {
//				if (interference.threadcounter().getThreadInstances().getOrDefault(ownerThread, 0) == 0) {
//					updatedStates.add(singleState);
//					continue;
//				}
//				final Set<Integer> possibleInterferingLocations = singleState.abstractLocationState().getTracker()
//						.getLocationForThread(interferenceThreadName);
//				final int interferenceLocation = mAbstractLocationMap
//						.getAbstractLocation(interference.action().getSource());
//
//				if (!possibleInterferingLocations.contains(interferenceLocation) && singleState.threadCounter()
//						.getThreadInstances().getOrDefault(interferenceThreadName, 0) == 1) {
//					updatedStates.add(singleState);
//					continue;
//				}
//
//				final GuardedInterferenceDomainState<STATE, LOC> movedState = singleState.movedTo(
//						interferenceThreadName,
//						mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
//
//				if (movedState.state().isBottom()) {
//					updatedStates.add(singleState);
//					continue;
//				}
//
//				final int before = possibleInterferingLocations.size();
//				final int after = movedState.abstractLocationState().getTracker()
//						.getLocationForThread(interferenceThreadName).size();
//				if (before < after) {
//					mForked = true;
//				}
//
//				if (interference.action() instanceof final ForkThreadCurrent fork) {
//					final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> forkedResult = handleFork(
//							new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE, Set.of(movedState)),
//							fork);
//					for (final GuardedInterferenceDomainState<STATE, LOC> st : forkedResult.getStates()) {
//						if (!st.state().isBottom()) {
//							updatedStates.add(st);
//						}
//					}
//				} else {
//					final var pair = new InterferenceStatePair<>(interference, singleState.state());
//					final var postStateUnderlying = computeOrGetPoststate(interference,
//							new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE, Set.of(movedState)),
//							pair);
//
//					if (postStateUnderlying.isEmpty()) {
//						updatedStates.add(movedState);
//					} else {
//						final Set<GuardedInterferenceDomainState<STATE, LOC>> postStates = postStateUnderlying.stream()
//								.filter(x -> !x.isBottom()) // Filter bottom underlying states
//								.map(x -> new GuardedInterferenceDomainState<>(x, movedState.threadCounter(),
//										movedState.abstractLocationState()))
//								.filter(st -> !st.state().isBottom()) // Filter if the wrapped state is bottom
//								.collect(Collectors.toSet());
//
//						if (postStates.isEmpty()) {
//							updatedStates.add(movedState);
//						} else {
//							final var postState = new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE,
//									postStates);
//							if (mIterations < MAXITF) {
//								// union them with the movedState
//								final var unioned = postState.union(new GuardedInterferenceDomainStateDisj<>(
//										mUnderlyingDomain, MAXSIZE, Set.of(movedState)));
//								for (final GuardedInterferenceDomainState<STATE, LOC> st : unioned.getStates()) {
//									if (!st.state().isBottom()) {
//										updatedStates.add(st);
//									}
//								}
//							} else {
//								final var widened = mGuardedInterferenceDomain.getWideningOperator()
//										.apply(new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, MAXSIZE,
//												Set.of(movedState)), postState);
//								for (final GuardedInterferenceDomainState<STATE, LOC> st : widened.getStates()) {
//									if (!st.state().isBottom()) {
//										updatedStates.add(st);
//									}
//								}
//							}
//							mInterferenceCache.put(pair, movedState.state());
//						}
//					}
//				}
//			}
//
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> nextRound = new GuardedInterferenceDomainStateDisj<>(
//					mUnderlyingDomain, MAXSIZE, updatedStates);
//			if (nextRound.isBottom()) {
//				return nextRound;
//			}
//			current = nextRound;
//		}
//		return current;
//	}
//
////	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> stateAfterInterferences(
////			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final String ownerThread) {
////
////		// this check might cost more time than it saves, if we don't encounter a lot of top-states
////		final var topstate = mUnderlyingDomain.createTopState();
////		if (topstate.addVariables(DataStructureUtils.difference(oldstate.getVariables(), topstate.getVariables()))
////				.isSubsetOf(oldstate.getUnderlyingState()) != SubsetResult.NONE) {
////			return oldstate;
////		}
////
////		// compute which threads can interfere in this state
////		final Set<String> threadNameSet = oldstate.getThreadInstanceState().getThreadNameSet();
////		final Set<String> possibleInterferenceSet = new HashSet<>();
////		final var procedureMap = oldstate.getThreadInstanceState().getThreadInstances();
////		for (final String threadName : threadNameSet) {
////			final int threadInstances = procedureMap.get(threadName);
////			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
////				possibleInterferenceSet.add(threadName);
////			}
////		}
////
////		return oldstate.union(interferenceFixpoint(possibleInterferenceSet, oldstate, ownerThread));
////	}
////
////	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
////			Interference<STATE, ACTION> interf, STATE targetState) {
////	}
////
////	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> interferenceFixpoint(
////			final Set<String> interferingThreads, final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> state,
////			final String ownerThread) {
////		mIterations = 0;
////		var newState = state;
////		mForked = false;
////		while (true) {
////			mIterations++;
////			// state just to check if fixpoint reached
////			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> beginLoopState = new GuardedInterferenceDomainStateDisj<>(
////					mUnderlyingDomain, newState.getUnderlyingState(), newState.getThreadInstanceState(),
////					newState.getAbstractLocationState());
////
////			for (final String interferenceThreadName : interferingThreads) {
////				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
////				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
////					continue;
////				}
////				newState = newState
////						.union(applyInterferences(newState, interferences, ownerThread, interferenceThreadName));
////			}
////			final boolean changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
////			if (!changed) {
////				break;
////			}
////		}
////		if (mForked) {
////			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
////			return newState.union(stateAfterInterferences(newState, ownerThread));
////		}
////		return newState;
////	}
////
////	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> applyInterferences(
////			GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState,
////			final Set<Interference<STATE, ACTION>> interferences, final String ownerThread,
////			final String interferenceThreadName) {
////		for (final Interference<STATE, ACTION> interference : interferences) {
////			// do the checks if interference is applicable
////			// 1. check threadcounter (is interfering thread alive in our state?)
////			if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
////				continue;
////			}
////			// 2. check abstract locations (is interfering thread in location where it matches the interference
////			// action)
////			final Set<Integer> possibleInterferingLocations = newState.getAbstractLocationState().getTracker()
////					.getLocationForThread(interferenceThreadName);
////			final int interferenceLocation = mAbstractLocationMap
////					.getAbstractLocation(interference.action().getSource());
////			if (!possibleInterferingLocations.contains(interferenceLocation)
////					&& newState.getThreadInstanceState().getThreadInstances().get(interferenceThreadName) == 1) {
////				continue;
////			}
////			mLogger.warn("Applying interference: " + interference.action() + "to state: " + newState.toLogString());
////			mLogger.warn("ownderThread " + ownerThread + "interfering Thread" + interferenceThreadName);
////			final int before = newState.getAbstractLocationState().getTracker()
////					.getLocationForThread(interferenceThreadName).size();
////			newState = newState.union(newState.movedTo(interferenceThreadName,
////					mAbstractLocationMap.getAbstractLocation(interference.action().getTarget())));
////			final int after = newState.getAbstractLocationState().getTracker()
////					.getLocationForThread(interferenceThreadName).size();
////			if (before < after) {
////				mForked = true;
////			}
////			if (interference.action() instanceof final ForkThreadCurrent fork) {
////				newState = newState.union(handleFork(newState, fork));
////				continue;
////			}
////			final var pair = new InterferenceStatePair<>(interference, newState.getUnderlyingState());
////
////			final var postStateUnderlying = computeOrGetPoststate(interference, newState, pair);
////			// empty when we encountered bottomstate
////			if (postStateUnderlying.isEmpty()) {
////				mLogger.error("EMPTY");
////				continue;
////			}
////			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postState = new GuardedInterferenceDomainStateDisj<>(
////					mUnderlyingDomain, postStateUnderlying, newState.getThreadInstanceState(),
////					newState.getAbstractLocationState());
////
////			if (mIterations < MAXITF) {
////				newState = newState.union(postState);
////				mLogger.warn("result: " + newState);
////			} else {
////				newState = mGuardedInterferenceDomain.getWideningOperator().apply(newState, postState);
////				mLogger.warn("DID POSTOPERATOR WIDENING: " + newState);
////			}
////			if (newState.isBottom()) {
////				return newState;
////			}
////			mInterferenceCache.put(pair, newState.getUnderlyingState());
////		}
////		return newState;
////
////	}
//
//	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> handleFork(
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState, final ForkThreadCurrent fork) {
//		final String forkedName = fork.getNameOfForkedProcedure();
//		final Map<String, Integer> mergedBefore = new HashMap<>();
//		for (final GuardedInterferenceDomainState<STATE, LOC> single : newState.getStates()) {
//			single.threadCounter().getThreadInstances().forEach((k, v) -> mergedBefore.merge(k, v, Math::max));
//		}
//		final int beforeFork = mergedBefore.getOrDefault(forkedName, 0);
//
//		final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> incremented = newState.incrementThread(forkedName);
//		final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> unioned = newState.union(incremented);
//
//		final Map<String, Integer> mergedAfter = new HashMap<>();
//		for (final GuardedInterferenceDomainState<STATE, LOC> single : unioned.getStates()) {
//			single.threadCounter().getThreadInstances().forEach((k, v) -> mergedAfter.merge(k, v, Math::max));
//		}
//		final int afterFork = mergedAfter.getOrDefault(forkedName, 0);
//
//		if (beforeFork < afterFork) {
//			mForked = true;
//		}
//		return unioned;
//	}
//
//	private Collection<STATE> computeOrGetPoststate(final Interference<STATE, ACTION> interference,
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState,
//			final InterferenceStatePair<STATE, ACTION, LOC> pair) {
//
//		if (mInterferenceCache.get(pair) != null) {
//			mLogger.error("Using cached state computation");
//			return List.of(mInterferenceCache.get(pair));
//		}
//
//		final STATE interferingState = interference.state();
//		if (interferingState.isBottom() || newState.isBottom()) {
//			return Collections.emptyList();
//		}
//
//		final List<STATE> resultList = new ArrayList<>();
//
//		for (final GuardedInterferenceDomainState<STATE, LOC> single : newState.getStates()) {
//			if (single.state().isBottom()) {
//				continue;
//			}
//
//			final var missingLocals = DataStructureUtils.difference(single.state().getVariables(),
//					interferingState.getVariables());
//			final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
//					single.state().getVariables());
//
//			final STATE lhs = single.state().addVariables(missingLocals2);
//			final STATE rhs = interferingState.addVariables(missingLocals);
//			final STATE intersectionState = lhs.intersect(rhs);
//
//			if (intersectionState.isBottom()) {
//				continue;
//			}
//
//			Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, interference.action());
//			postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
//
//			resultList.addAll(postState);
//		}
//
//		if (!resultList.isEmpty()) {
//			mInterferenceCache.put(pair, resultList.iterator().next());
//		}
//
//		return resultList;
//	}
//
//	@Override
//	public List<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> apply(
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> stateBeforeLeaving,
//			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> secondState, final ACTION transition) {
//		throw new UnsupportedOperationException("Not implemented.");
//	}
//
//	@Override
//	public EvalResult evaluate(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> state, final Term formula,
//			final Script script) {
//		throw new UnsupportedOperationException("Not implemented.");
//	}
//}
