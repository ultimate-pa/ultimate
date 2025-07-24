package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;

public class DisjunctiveGuardedStateFactory<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractStateStorage<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final int mMaxParallelStates;
	private final Map<String, ? extends LOC> mEntryLocs;
	final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> mForksInLoop;
	private final GuardedInterferenceCache<UNDERLYINGSTATE, ACTION, LOC> mCache;

	public DisjunctiveGuardedStateFactory(
			final IAbstractStateStorage<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> stateStorage,
			final ConcurrentIcfgAnalyzer<ACTION, LOC> analyzer, final int maxStates,
			final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> domain,
			final Map<String, ? extends LOC> entryLocs, final IIcfg<? extends LOC> icfg,
			final GuardedInterferenceCache<UNDERLYINGSTATE, ACTION, LOC> cache) {
		mStateStorage = stateStorage;
		mAnalyzer = analyzer;
		mMaxParallelStates = maxStates;
		mDomain = domain;
		mEntryLocs = entryLocs;
		mForksInLoop = IcfgUtils.getForksInLoop(icfg);
		mCache = cache;
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> getInitialState(
			final String procedure, final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences) {
		final var allForkLocs = new HashSet<LOC>();
		final var multipleForkLocs = new HashSet<LOC>();
		var result = combineForkingStates(procedure, allForkLocs, multipleForkLocs);

		if (result != null) {
			for (final LOC loc : allForkLocs) {
				final var edge = loc.getOutgoingEdges().iterator().next();
				if (edge instanceof final ForkThreadCurrent fork) {
					final var forkUsedMultipleTimes = mForksInLoop.contains(fork) || multipleForkLocs.contains(loc);
					result = GuardedStateTransformer.assignForkId(procedure,
							fork.getForkStatement().getThreadID().length, loc, forkUsedMultipleTimes, result);
				}
			}
			final boolean multipleThreads = wasForkedMultipleTimes(allForkLocs);
			final var forkedInitialState = constructForkedInitialState(result, procedure, multipleThreads,
					interferences);
			return forkedInitialState;
		}
		// no forking threads, construct fresh state (must be main/start-thread)
		return mainThreadEntryState(procedure);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> combineForkingStates(
			final String procedure, final HashSet<LOC> allForkLocs, final HashSet<LOC> multipliedForks) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = new HashSet<>();
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final var state = mStateStorage.getAbstractState(loc);
			if (state == null) {
				return null;
			}
			if (state.getSingleState(GuardedInterferenceDomainState::union).threadCounter().getThreadInstances()
					.get(loc.getProcedure()) > 1) {
				multipliedForks.add(loc);
			}
			allForkLocs.add(loc);
			final var movedState = translateForkLocIntoInitialState(loc, state, procedure);
			final var clearedState = removeLocalVars(movedState);
			forkStates.addAll(clearedState.getStates());
		}
		if (forkStates.isEmpty()) {
			return null;
		}
		return DisjunctiveAbstractState.createDisjunction(forkStates, mMaxParallelStates);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateForkLocIntoInitialState(
			final LOC loc,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> inputState,
			final String procedure) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateDomainStates = new HashSet<>();
		final var globalImmutableMap = inputState.getStates().iterator().next().abstractLocationState()
				.getLocationMap();
		final var proceduresEntryLoc = globalImmutableMap.getEntryLoc(procedure);
		// TODO: unsafe
		final var afterForkLocation = globalImmutableMap.getAbstractLocation((LOC) loc.getOutgoingNodes().getFirst());
		for (final var singleState : inputState.getStates()) {
			final var executedFork = singleState.movedTo(loc.getProcedure(), afterForkLocation);
			final var movedOwnershipLocation = new AbstractLocationState<>(proceduresEntryLoc,
					executedFork.abstractLocationState());
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> movedOwnership = new GuardedInterferenceDomainState<>(
					executedFork.state(), executedFork.threadCounter(), movedOwnershipLocation);
			translateDomainStates.add(movedOwnership);
		}
		return DisjunctiveAbstractState.createDisjunction(translateDomainStates, mMaxParallelStates);
	}

	private boolean wasForkedMultipleTimes(final HashSet<LOC> allForkLocs) {
		int forks = 0;
		boolean isCircular = false;
		for (final LOC forkLoc : allForkLocs) {
			forks++;
			for (final IcfgEdge forkEdge : forkLoc.getOutgoingEdges()) {
				if (forkEdge instanceof final ForkThreadCurrent fork1) {
					final boolean circular = mForksInLoop.contains(fork1);
					if (circular) {
						isCircular = true;
						break;
					}
				}
			}
		}
		if (forks > 1 || isCircular) {
			return true;
		}
		return false;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> mainThreadEntryState(
			final String procedure) {
		var bottomState = mDomain.createBottomPreconditionState();
		bottomState = bottomState.assignForkId(procedure, 0, null, false);
		final var locMap = mDomain.getAbstractLocationMap();
		final var entryLoc = mEntryLocs.get(procedure);
		bottomState = bottomState.initializeLocation(entryLoc, locMap,
				mAnalyzer.getTopologicalProcedureOrder().stream().collect(Collectors.toSet()));
		return new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> constructForkedInitialState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result,
			final String procedure, final boolean multipleThreads,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = result.getStates();
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> initialStates = new HashSet<>();
		for (final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> forkState : forkStates) {
			// filter only states from forking threads whwere forked thread still at start position
			// (we would do self interference by proxy otherwise
			final var entryLoc = forkState.abstractLocationState().getTracker().getLocationForThread(procedure);
			final var globalMap = forkState.abstractLocationState().getLocationMap();
			if (entryLoc.contains(globalMap.getAbstractLocation(mEntryLocs.get(procedure)))) {
				initialStates.add(removeLocalVars(forkState));
			} else if (multipleThreads) {
				initialStates.add(removeLocalVars(forkState));
			}
		}
		final var applier = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator()).getItfApplier();
		final var cleanedStart = DisjunctiveAbstractState.createDisjunction(initialStates, mMaxParallelStates);
		final var interferenceDomainDisj = applier.stateAfterInterferences(cleanedStart, procedure, mCache);
		return interferenceDomainDisj;
	}

	private GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> removeLocalVars(
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> singleStateRecord) {
		final List<IProgramVarOrConst> varsToRemove = singleStateRecord.state().getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return singleStateRecord;
		}
		return new GuardedInterferenceDomainState<>(singleStateRecord.state().removeVariables(varsToRemove),
				singleStateRecord.threadCounter(), singleStateRecord.abstractLocationState());
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> removeLocalVars(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> state) {
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return state;
		}
		return state.removeVariables(varsToRemove);
	}
}
