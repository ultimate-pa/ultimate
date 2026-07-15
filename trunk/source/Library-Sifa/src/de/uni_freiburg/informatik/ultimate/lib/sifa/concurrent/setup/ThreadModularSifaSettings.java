package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceApplicatorType interferenceApplicatorType,
		int outerWideningThreshold, int innerWideningThreshold, boolean joinPrecision, boolean useBuckets,
		boolean locksetAwareInterference, boolean publishOnAcquire, boolean proofCheck,
		boolean resultPrint, int maxBuckets, int maxDisjunctsPerBucket) {

	public static final int DEFAULT_MAX_BUCKETS = 10;
	public static final int DEFAULT_MAX_DISJUNCTS_PER_BUCKET = 2;

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	public enum InterferenceApplicatorType {
		STRONGEST_POSTCONDITION, PREPOST, GUARDED_EXACT_UPDATE, POST_STATE, UNARY_GLOBALS, NONE
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}
}
