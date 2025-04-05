// package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;
//
// import java.util.Collection;
// import java.util.Collections;
// import java.util.HashMap;
// import java.util.HashSet;
// import java.util.List;
// import java.util.Map;
// import java.util.Set;
// import java.util.stream.Collectors;
//
// import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
// import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
// import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
// import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
//
// public class GuardedInterferenceHandler<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC
// extends IcfgLocation> {
// private final ILogger mLogger;
//
// private final AbstractInterferenceState<STATE, ACTION> mInterferences;
// private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
// private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
// private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
//
// private final int MAXITF = 9;
// private int mIterations;
// private boolean mForked = false;
// private final Map<InterferenceStatePair<STATE, ACTION, LOC>, STATE> mInterferenceCache = new HashMap<>();
//
// public GuardedInterferenceHandler(final IIcfg<?> cfg, final ILogger logger,
// final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
// final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
// final AbstractInterferenceState<STATE, ACTION> interferenceState) {
// mLogger = logger;
// mUnderlyingDomain = underlying;
// mUnderlyingPostOp = postOp;
// mGuardedInterferenceDomain = relationalInterferingDomain;
// mInterferences = interferenceState;
// }
//
// private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC
// extends IcfgLocation>(
// Interference<STATE, ACTION> interf, STATE targetState) {
// }
//
// public GuardedInterferenceDomainState<STATE, ACTION, LOC> stateAfterInterferences(
// final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final String ownerThread) {
//
// // this check might cost more time than it saves, if we don't encounter a lot of top-states
// final var topstate = mUnderlyingDomain.createTopState();
// if (topstate.addVariables(DataStructureUtils.difference(oldstate.getVariables(), topstate.getVariables()))
// .isSubsetOf(oldstate.getUnderlyingState()) != SubsetResult.NONE) {
// return oldstate;
// }
//
// // compute which threads can interfere in this state
// final Set<String> threadNameSet = oldstate.getThreadInstanceState().getThreadNameSet();
// final Set<String> possibleInterferenceSet = new HashSet<>();
// final var procedureMap = oldstate.getThreadInstanceState().getThreadInstances();
// for (final String threadName : threadNameSet) {
// final int threadInstances = procedureMap.get(threadName);
// if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
// possibleInterferenceSet.add(threadName);
// }
// }
//
// return oldstate.union(interferenceFixpoint(possibleInterferenceSet, oldstate, ownerThread));
// }
//
// private GuardedInterferenceDomainState<STATE, ACTION, LOC> interferenceFixpoint(
// final Set<String> interferingThreads, final GuardedInterferenceDomainState<STATE, ACTION, LOC> state,
// final String ownerThread) {
// mIterations = 0;
// var newState = state;
// mForked = false;
// while (true) {
// mIterations++;
// // state just to check if fixpoint reached
// final var beginLoopState =
// new GuardedInterferenceDomainState<>(mUnderlyingDomain, newState.getUnderlyingState(),
// newState.getThreadInstanceState(), newState.getAbstractLocationState());
//
// for (final String interferenceThreadName : interferingThreads) {
// final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
// if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
// continue;
// }
// newState = newState.union(applyInterferences(newState, interferences, ownerThread));
// }
// final boolean changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
// if (!changed) {
// break;
// }
// }
// mLogger.info("state after interferences: " + newState);
// if (mForked) {
// // TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
// return newState.union(stateAfterInterferences(newState, ownerThread));
// }
// return newState;
// }
//
// private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyInterferences(
// GuardedInterferenceDomainState<STATE, ACTION, LOC> newState,
// final Set<Interference<STATE, ACTION>> interferences, final String ownerThread) {
// for (final Interference<STATE, ACTION> interference : interferences) {
// if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
// continue;
// }
// mLogger.info("Applying interference: " + interference.toString() + "to state: " + newState.toLogString());
//
// if (interference.action() instanceof final ForkThreadCurrent fork) {
// newState = newState.union(handleFork(newState, fork));
// continue;
// }
//
// final var pair = new InterferenceStatePair<>(interference, newState.getUnderlyingState());
// final var postStateUnderlying = computeOrGetPoststate(interference, newState, pair);
// // empty when we encountered bottomstate
// if (postStateUnderlying.isEmpty()) {
// continue;
// }
// final var postState = new GuardedInterferenceDomainState<>(mUnderlyingDomain, postStateUnderlying,
// newState.getThreadInstanceState(), newState.getAbstractLocationState());
//
// if (mIterations < MAXITF) {
// newState = newState.union(postState);
// mLogger.info("result: " + newState);
// } else {
// newState = mGuardedInterferenceDomain.getWideningOperator().apply(newState, postState);
// mLogger.warn("DID POSTOPERATOR WIDENING: " + newState);
// }
// if (newState.isBottom()) {
// return newState;
// }
// mInterferenceCache.put(pair, newState.getUnderlyingState());
// }
// return newState;
// }
//
// private GuardedInterferenceDomainState<STATE, ACTION, LOC>
// handleFork(GuardedInterferenceDomainState<STATE, ACTION, LOC> newState, final ForkThreadCurrent fork) {
// final int beforeFork =
// newState.getThreadInstanceState().getThreadInstances().get(fork.getNameOfForkedProcedure());
// newState = newState.union(newState.incrementThread(fork.getNameOfForkedProcedure()));
// final int afterFork =
// newState.getThreadInstanceState().getThreadInstances().get(fork.getNameOfForkedProcedure());
// if (beforeFork < afterFork) {
// mForked = true;
// }
// return newState;
// }
//
// private Collection<STATE> computeOrGetPoststate(final Interference<STATE, ACTION> interference,
// final GuardedInterferenceDomainState<STATE, ACTION, LOC> newState,
// final InterferenceStatePair<STATE, ACTION, LOC> pair) {
//
// // if in cache, return state with cached underlying state without applying postOp
// if (mInterferenceCache.get(pair) != null) {
// mLogger.error("Using cached state computation");
// return List.of(mInterferenceCache.get(pair));
// }
//
// // add variables to both states to be able to intersect
// final STATE interferingState = interference.state();
// final var missingLocals =
// DataStructureUtils.difference(newState.getVariables(), interferingState.getVariables());
// final var missingLocals2 =
// DataStructureUtils.difference(interferingState.getVariables(), newState.getVariables());
// if (newState.getUnderlyingState().isBottom() || interferingState.isBottom()) {
// return Collections.emptyList();
// }
// final STATE intersectionState = newState.getUnderlyingState().addVariables(missingLocals2)
// .intersect(interferingState.addVariables(missingLocals));
// if (intersectionState.isBottom()) {
// return Collections.emptyList();
// }
//
// // apply underlying postOp
// Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, interference.action());
// postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
// return postState;
// }
// }
