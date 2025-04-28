package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;

public class InterferenceCreator {

	public static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> computeInterferences(
			final Map<String, ? extends LOC> mEntryLocs, final IIcfg<? extends LOC> icfg,
			final IAbstractStateStorage<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage,
			final ITransitionProvider<ACTION, LOC> mTransitionProvider, final int maxSize,
			final AbstractLocationMap<LOC> mLocationAbstraction,
			final LocationAbstraction<LOC> locationAbstractionCalculator) {
		// do we want multiple guardedStates to be represented in an interference prestate, or just the union
		// Seems to not make much difference in state amount actually
		final boolean precise = false;
		final var unionOp = new GuardedStateUnionOperator<UNDERLYINGSTATE, ACTION, LOC>();
		final var result = new AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC>(
				icfg.getCfgSmtToolkit().getProcedures());
		for (final LOC entryLoc : mEntryLocs.values()) {
			new IcfgLocationIterator<>(entryLoc).forEachRemaining(loc -> {
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					if (!isInterferingTransition((ACTION) edge, icfg, mLocationAbstraction,
							locationAbstractionCalculator, loc)) {
						continue;
					}
					final var preState = mStateStorage.getAbstractState(mTransitionProvider.getSource((ACTION) edge));
					if (preState == null) {
						continue;
					}
					final var interference = computeInterference(precise, preState, edge, unionOp, maxSize);
					result.addInterference(entryLoc.getProcedure(), interference);
				}
			});
		}
		return result;
	}

	private static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Interference<UNDERLYINGSTATE, ACTION, LOC> computeInterference(
			final boolean precise,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preState,
			final IcfgEdge edge, final GuardedStateUnionOperator<UNDERLYINGSTATE, ACTION, LOC> unionOp,
			final int maxSize) {
		final Interference<UNDERLYINGSTATE, ACTION, LOC> interference;
		if (precise) {
			final var reduced = reduceInterferencePrestate(preState, maxSize);
			interference = new Interference<>((ACTION) edge, reduced);
		} else {
			interference = new Interference<>((ACTION) edge,
					new DisjunctiveAbstractState<>(maxSize, preState.getSingleState(unionOp)));
		}
		return interference;
	}

	private static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> reduceInterferencePrestate(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preState,
			final int maxSize) {
		final var states = preState.getStates();
		if (states.size() <= 1) {
			return preState;
		}
		final List<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> toProcess = new ArrayList<>(states);
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result = new HashSet<>();
		final int startingLen = toProcess.size();
		while (!toProcess.isEmpty()) {
			GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> base = toProcess.remove(toProcess.size() - 1);
			final ListIterator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> it = toProcess
					.listIterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> candidate = it.next();
				if (base.state().isEqualTo(candidate.state())) {
					base = base.union(candidate);
					it.remove();
				}
			}
			result.add(base);
		}
		final int endLen = result.size();
		return DisjunctiveAbstractState.createDisjunction(result, maxSize);
	}

	// with naive location abstraction we cannot skip any interferences, even if they are a "skip"
	private static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> boolean isInterferingTransition(
			final ACTION transition, final IIcfg<? extends LOC> icfg,
			final AbstractLocationMap<LOC> mLocationAbstraction,
			final LocationAbstraction<LOC> locationAbstractionCalculator, final LOC loc) {
		if (mLocationAbstraction.getAbstractLocation(transition.getSource()) != mLocationAbstraction
				.getAbstractLocation(transition.getTarget())) {
			return true;
		}
		if (locationAbstractionCalculator.shouldDifferentiate(loc.getOutgoingEdges())) {
			return true;
		}
		final var globals = icfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		if ((transition.getTransformula().getOutVars().keySet().stream().anyMatch(globals::contains))) {
			return true;
		}
		if (transition instanceof ForkThreadCurrent) {
			return true;
		}
		return false;
	}
}
