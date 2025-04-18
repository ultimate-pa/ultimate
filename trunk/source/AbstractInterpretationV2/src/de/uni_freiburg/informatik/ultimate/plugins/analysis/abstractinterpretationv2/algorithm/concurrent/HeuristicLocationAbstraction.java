package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class HeuristicLocationAbstraction {
	private static int locationCounter = 0;

	public static <LOC extends IcfgLocation> AbstractLocationMap<LOC> computeLocationAbstraction(
			final String locationAbstraction, final IIcfg<? extends LOC> icfg) {
		final Map<String, ? extends LOC> entryLocs = icfg.getProcedureEntryNodes();
		final AbstractLocationMap<LOC> absMap = switch (locationAbstraction) {
		case "Singleton" -> new AbstractLocationMap<>((l -> 1), entryLocs);
		case "Fully precise" -> new AbstractLocationMap<>((l -> locationCounter++), entryLocs);
		case "Heuristic splitting" -> new AbstractLocationMap<>(l -> {
			final var incoming = l.getIncomingEdges();
			for (final IcfgEdge icfgEdge : incoming) {
				if (shouldDifferentiate(icfgEdge.getTransformula())) {
					return locationCounter++;
				}
			}
			return locationCounter;
		}, entryLocs);
		default -> new AbstractLocationMap<>((l -> 1), entryLocs);
		};
		return absMap;
	}

	private static boolean shouldDifferentiate(final UnmodifiableTransFormula transformula) {
		// TODO Auto-generated method stub
		return false;
	}

}
