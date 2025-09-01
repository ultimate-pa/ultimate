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

public class InterferenceCreator<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	public InterferenceCreator() {
	}

	public AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> computeInterferences(
			final Map<String, ? extends LOC> mEntryLocs, final IIcfg<? extends LOC> icfg,
			final IAbstractStateStorage<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage,
			final ITransitionProvider<ACTION, LOC> mTransitionProvider,
			final StaticAbstractLocationMap<LOC> mLocationAbstraction) {
		// do we want multiple guardedStates to be represented in an interference prestate, or just the union
		// Seems to not make much difference in state amount actually
		final var result = new AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC>(
				icfg.getCfgSmtToolkit().getProcedures());
		for (final LOC entryLoc : mEntryLocs.values()) {
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					if (!isInterferingTransition((ACTION) edge, icfg, mLocationAbstraction)) {
						continue;
					}
					var disjPreState = mStateStorage
							.getAbstractState(mTransitionProvider.getSource((ACTION) edge));
					if (InterferenceFIxpoint.postOnly) {
					disjPreState = mStateStorage
							.getAbstractState(mTransitionProvider.getTarget((ACTION) edge));
						
					}
					if (disjPreState == null) {
						continue;
					}
					final var interference = computeInterference(disjPreState, edge);
					result.addInterference(interference);
				}
			}
		}
		return result;
	}

	private Interference<UNDERLYINGSTATE, ACTION, LOC> computeInterference(
			final DisjunctiveAbstractState<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preState,
			final IcfgEdge edge) {
		final Interference<UNDERLYINGSTATE, ACTION, LOC> interference;
		{
			interference = new Interference<>((ACTION) edge, preState.getSingleState(InterferenceDomainState::union));
		}
		return interference;
	}

	// with naive location abstraction we cannot skip any interferences, even if they are a "skip"
	private boolean isInterferingTransition(final ACTION transition, final IIcfg<? extends LOC> icfg,
			final StaticAbstractLocationMap<LOC> mLocationAbstraction) {
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
