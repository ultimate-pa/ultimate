package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;

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
			final LocationAbstraction<LOC> locationAbstractionCalculator, final String precision) {
		// do we want multiple guardedStates to be represented in an interference prestate, or just the union
		// Seems to not make much difference in state amount actually
		final boolean precise;
		if (precision.equals("Unioned")) {
			precise = false;
		} else {
			precise = true;
		}
		final var result = new AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC>(
				icfg.getCfgSmtToolkit().getProcedures());
		for (final LOC entryLoc : mEntryLocs.values()) {
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					if (!isInterferingTransition((ACTION) edge, icfg, mLocationAbstraction,
							locationAbstractionCalculator, loc)) {
						continue;
					}
					final var preState = mStateStorage.getAbstractState(mTransitionProvider.getSource((ACTION) edge));
					if (preState == null) {
						continue;
					}
					final var interference = computeInterference(precise, preState, edge, maxSize);
					result.addInterference(interference);
				}
			}
		}
		return result;
	}

	private static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Interference<UNDERLYINGSTATE, ACTION, LOC> computeInterference(
			final boolean precise,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preState,
			final IcfgEdge edge, final int maxSize) {
		final Interference<UNDERLYINGSTATE, ACTION, LOC> interference;
		if (precise) {
			interference = new Interference<>((ACTION) edge, preState);
		} else {
			interference = new Interference<>((ACTION) edge, new DisjunctiveAbstractState<>(maxSize,
					preState.getSingleState(GuardedInterferenceDomainState::union)));
		}
		return interference;
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
		final var globals = icfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		if ((transition.getTransformula().getAssignedVars().stream().anyMatch(globals::contains))) {
			return true;
		}
		if (transition instanceof ForkThreadCurrent) {
			return true;
		}
		return false;
	}
}
