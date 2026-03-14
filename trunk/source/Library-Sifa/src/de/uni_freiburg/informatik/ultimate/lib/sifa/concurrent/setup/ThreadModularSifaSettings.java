package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceType interferenceType, int outerWideningThreshold,
		int innerWideningThreshold, boolean joinPrecision) {

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	public enum InterferenceType {
		PER_THREAD, PER_EDGE, PER_ABSTRACT_LOCATION
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}

	public ThreadModularSifaSettings(final boolean useGhostLocations,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final int outerWideningThreshold, final int innerWideningThreshold) {
		this(useGhostLocations ? LocationTrackingMode.GHOST_VARIABLES : LocationTrackingMode.NONE,
				locationAbstractionType, interferenceType, outerWideningThreshold, innerWideningThreshold, true);
	}
}