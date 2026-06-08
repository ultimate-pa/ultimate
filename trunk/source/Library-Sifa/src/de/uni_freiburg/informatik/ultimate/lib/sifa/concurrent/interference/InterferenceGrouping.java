package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;

public final class InterferenceGrouping {

	public record AbstractLocationPair(int sourceAbstractLocation, int targetAbstractLocation) {
	}

	public record ThreadedKey(String threadId, AbstractLocationPair pair) {
	}

	private InterferenceGrouping() {
	}

	public static AbstractLocationPair keyFor(final TransFormulaToInterferencePredicate translator,
			final IcfgLocation source, final IcfgLocation target) {
		return new AbstractLocationPair(checkAbstractLocationId(translator, source),
				checkAbstractLocationId(translator, target));
	}

	private static int checkAbstractLocationId(final TransFormulaToInterferencePredicate translator,
			final IcfgLocation location) {
		final Integer abstractLocationId = translator.getAbstractLocationIdOrNull(location);
		if (abstractLocationId == null) {
			throw new IllegalStateException("Missing abstract location ID for " + location);
		}
		return abstractLocationId;
	}
}
