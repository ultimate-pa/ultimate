package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceApplicatorType interferenceApplicatorType,
		int outerWideningThreshold, int innerWideningThreshold, boolean joinPrecision, boolean useBuckets,
		boolean guardBucketSplit, boolean proofCheck, boolean resultPrint) {

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	/** How collected interference predicates are applied. */
	public enum InterferenceApplicatorType {
		STRONGEST_POSTCONDITION, PREPOST, GUARDED_EXACT_UPDATE, POST_STATE, UNARY_GLOBALS, NONE
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}

	public ThreadModularSifaSettings(final boolean useGhostLocations,
			final LocationAbstractionType locationAbstractionType, final int outerWideningThreshold,
			final int innerWideningThreshold) {
		this(useGhostLocations ? LocationTrackingMode.GHOST_VARIABLES : LocationTrackingMode.NONE,
				locationAbstractionType, InterferenceApplicatorType.STRONGEST_POSTCONDITION, outerWideningThreshold,
				innerWideningThreshold, false, true, false, false, false);
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType, final int outerWideningThreshold,
			final int innerWideningThreshold, final boolean joinPrecision) {
		this(locationTrackingMode, locationAbstractionType, InterferenceApplicatorType.STRONGEST_POSTCONDITION,
				outerWideningThreshold, innerWideningThreshold, joinPrecision, true, false, false, false);
	}
}
