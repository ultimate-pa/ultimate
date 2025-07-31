package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;

public class InitialStateFactory<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractStateStorage<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final InterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final int mMaxParallelStates;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final InterferenceCache<UNDERLYINGSTATE, ACTION, LOC> mCache;

	public InitialStateFactory(
			final IAbstractStateStorage<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> stateStorage,
			final ConcurrentIcfgAnalyzer<ACTION, LOC> analyzer, final int maxStates,
			final InterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> domain, final Map<String, ? extends LOC> entryLocs,
			final InterferenceCache<UNDERLYINGSTATE, ACTION, LOC> cache) {
		mStateStorage = stateStorage;
		mAnalyzer = analyzer;
		mMaxParallelStates = maxStates;
		mDomain = domain;
		mEntryLocs = entryLocs;
		mCache = cache;
	}

	public DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> createInitialStates(
			final String procedure) {
		final var allForkLocs = new HashSet<LOC>();
		final var result = applyPostopAndTranslateForkStates(procedure, allForkLocs);
		if (result != null) {
			final var forkedInitialState = filterStatesAndApplyItfs(result, procedure);
			return forkedInitialState;
		}
		// no forking threads, construct fresh state (must be main/start-thread)
		return mainThreadEntryState(procedure);
	}

	private DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> applyPostopAndTranslateForkStates(
			final String procedure, final HashSet<LOC> allForkLocs) {
		final Set<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = new HashSet<>();
		final InterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC> postOperator = (InterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator();
		for (final LOC initialLoc : mAnalyzer.getForkLocations(procedure)) {

			final var state = mStateStorage.getAbstractState(initialLoc);
			final var transition = (ACTION) initialLoc.getOutgoingEdges().iterator().next();
			if (state == null) {
				return null;
			}
			allForkLocs.add(initialLoc);
			final boolean selfInterfering = initialLoc.getProcedure().equals(procedure);
			final var movedState = translateForkLocIntoInitialState(state, procedure);
			final var afterForkStates = movedState.getStates().stream()
					.map(s -> new InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>(s.state(),
							postOperator.applyThreadCounter(s.threadCounter(), s.abstractLocationState(), transition),
							postOperator.applyAbstractLocation(s.abstractLocationState(), transition, selfInterfering,
									false)))
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

	private DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateForkLocIntoInitialState(
			final DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> inputState,
			final String procedure) {
		final Set<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateDomainStates = new HashSet<>();
		final var globalImmutableMap = inputState.getStates().iterator().next().abstractLocationState()
				.getLocationMap();
		final var abstractProceduresEntryLoc = globalImmutableMap.getAbstractEntryLoc(procedure);
		for (final var singleState : inputState.getStates()) {
			translateDomainStates
					.add(singleState.movedToInf(procedure, -1, abstractProceduresEntryLoc, abstractProceduresEntryLoc));
		}
		return DisjunctiveAbstractState.createDisjunction(translateDomainStates, mMaxParallelStates);
	}

	private DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> filterStatesAndApplyItfs(
			final DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result,
			final String procedure) {
		final Set<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = result.getStates();
		final Set<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translatedForkStates = new HashSet<>();
		for (final var forkState : forkStates) {
			// filter only states from forking threads whwere forked thread still at start position
			// (we would do self interference by proxy otherwise
			final var entryLoc = forkState.abstractLocationState().getTracker().getLocationForThread(procedure);
			final var globalMap = forkState.abstractLocationState().getLocationMap();
			// TODO: filter with forkids now instead
			if (entryLoc.contains(globalMap.getAbstractLocation(mEntryLocs.get(procedure)))) {
				translatedForkStates.add(forkState);
			}
		}
		final var applier = ((InterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain.getPostOperator())
				.getItfApplier();
		final var cleanedStart = DisjunctiveAbstractState.createDisjunction(translatedForkStates, mMaxParallelStates);
		final var interferenceDomainDisj = applier.computeInterferenceFixpoint(cleanedStart, procedure, mCache);
		return interferenceDomainDisj;
	}

	public DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> removeLocalVars(
			final DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> state) {
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return state;
		}
		return state.removeVariables(varsToRemove);
	}

	private DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> mainThreadEntryState(
			final String procedure) {
		var bottomState = mDomain.createBottomPreconditionState();
		bottomState = bottomState.assignForkId(procedure, 0, null, false);
		final var locMap = mDomain.getAbstractLocationMap();
		final var entryLoc = mEntryLocs.get(procedure);
		bottomState = bottomState.initializeLocation(entryLoc, locMap,
				mAnalyzer.getTopologicalProcedureOrder().stream().collect(Collectors.toSet()));
		return new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}
}
