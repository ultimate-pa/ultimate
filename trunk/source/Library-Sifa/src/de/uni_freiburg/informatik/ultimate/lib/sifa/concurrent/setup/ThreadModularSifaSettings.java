package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceType interferenceType,
		InterferenceApplicatorType interferenceApplicatorType, int outerWideningThreshold, int innerWideningThreshold,
		boolean joinPrecision, InterferenceMergeDomain interferenceMergeDomain, boolean guardBucketSplit) {

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	/** How interference predicates are grouped. */
	public enum InterferenceType {
		PER_THREAD, PER_EDGE, PER_ABSTRACT_LOCATION
	}

	/** How collected interference predicates are applied. */
	public enum InterferenceApplicatorType {
		QE, PREPOST, GUARDED_OVERWRITE, GUARDED_EXACT_UPDATE, POST_STATE
	}

	/** Domain for joining interference predicates during collection. */
	public enum InterferenceMergeDomain {
		SAME_AS_ANALYSIS,
		OCTAGON
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}

	public ThreadModularSifaSettings(final boolean useGhostLocations,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final int outerWideningThreshold, final int innerWideningThreshold) {
		this(useGhostLocations ? LocationTrackingMode.GHOST_VARIABLES : LocationTrackingMode.NONE,
				locationAbstractionType, interferenceType, InterferenceApplicatorType.QE, outerWideningThreshold,
				innerWideningThreshold, true, InterferenceMergeDomain.SAME_AS_ANALYSIS, false);
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final int outerWideningThreshold, final int innerWideningThreshold, final boolean joinPrecision) {
		this(locationTrackingMode, locationAbstractionType, interferenceType, InterferenceApplicatorType.QE,
				outerWideningThreshold, innerWideningThreshold, joinPrecision,
				InterferenceMergeDomain.SAME_AS_ANALYSIS, false);
	}
}
