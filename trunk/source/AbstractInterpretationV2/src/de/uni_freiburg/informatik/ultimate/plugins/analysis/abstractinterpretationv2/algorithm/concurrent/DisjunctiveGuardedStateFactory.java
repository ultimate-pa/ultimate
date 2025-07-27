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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;

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
			final String procedure) {
		final var allForkLocs = new HashSet<LOC>();
		final var result = combineForkingStates(procedure, allForkLocs);

		if (result != null) {
			final var forkedInitialState = constructForkedInitialState(result, procedure);
			return forkedInitialState;
		}
		// no forking threads, construct fresh state (must be main/start-thread)
		return mainThreadEntryState(procedure);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> combineForkingStates(
			final String procedure, final HashSet<LOC> allForkLocs) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = new HashSet<>();
		final GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC> postOperator = (GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator();
		for (final LOC initialLoc : mAnalyzer.getForkLocations(procedure)) {
//			final LOC afterForkLoc = (LOC) initialLoc.getOutgoingNodes().iterator().next();

			final var state = mStateStorage.getAbstractState(initialLoc);
			final var transition = (ACTION) initialLoc.getOutgoingEdges().iterator().next();
			if (state == null) {
				return null;
			}
			allForkLocs.add(initialLoc);
			final var movedState = translateForkLocIntoInitialState(state, procedure);
			final var afterForkStates = movedState.getStates().stream()
					.map(s -> new GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>(s.state(),
							postOperator.applyThreadCounter(s.threadCounter(), s.abstractLocationState(), transition),
							postOperator.applyAbstractLocation(s.abstractLocationState(), transition, false, false)))
					.toList();
			final var clearedState = removeLocalVars(
					DisjunctiveAbstractState.createDisjunction(afterForkStates, mMaxParallelStates));
			forkStates.addAll(clearedState.getStates());
		}
		if (forkStates.isEmpty()) {
			return null;
		}
		return DisjunctiveAbstractState.createDisjunction(forkStates, mMaxParallelStates);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateForkLocIntoInitialState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> inputState,
			final String procedure) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateDomainStates = new HashSet<>();
		final var globalImmutableMap = inputState.getStates().iterator().next().abstractLocationState()
				.getLocationMap();
		final var proceduresEntryLoc = globalImmutableMap.getEntryLoc(procedure);
		for (final var singleState : inputState.getStates()) {
			final var movedOwnershipLocation = new AbstractLocationState<>(proceduresEntryLoc,
					singleState.abstractLocationState());
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> movedOwnership = new GuardedInterferenceDomainState<>(
					singleState.state(), singleState.threadCounter(), movedOwnershipLocation);
			translateDomainStates.add(movedOwnership);
		}
		return DisjunctiveAbstractState.createDisjunction(translateDomainStates, mMaxParallelStates);
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
			final String procedure) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = result.getStates();
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translatedForkStates = new HashSet<>();
		for (final var forkState : forkStates) {
			// filter only states from forking threads whwere forked thread still at start position
			// (we would do self interference by proxy otherwise
			final var entryLoc = forkState.abstractLocationState().getTracker().getLocationForThread(procedure);
			final var globalMap = forkState.abstractLocationState().getLocationMap();
			// TODO: filter with forkids now instead
			if (entryLoc.contains(globalMap.getAbstractLocation(mEntryLocs.get(procedure)))) {
				translatedForkStates.add(removeLocalVars(forkState));
			}
		}
		final var applier = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator()).getItfApplier();
		final var cleanedStart = DisjunctiveAbstractState.createDisjunction(translatedForkStates, mMaxParallelStates);
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
