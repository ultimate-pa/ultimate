package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceType interferenceType,
		InterferenceRepresentation interferenceRepresentation, int outerWideningThreshold, int innerWideningThreshold,
		boolean joinPrecision, InterferenceMergeDomain interferenceMergeDomain) {

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	/** How interference predicates are grouped/bucketed (orthogonal to representation). */
	public enum InterferenceType {
		PER_THREAD, PER_EDGE, PER_ABSTRACT_LOCATION
	}

	/** How interference predicates are represented and applied. Ordered from cheapest to most precise. */
	public enum InterferenceRepresentation {
		POST_STATE, SYNTACTIC, SYNTACTIC_PRECISE, RELATIONAL_LIGHT, RELATIONAL_QE
	}

	/** Domain used for joining interference predicates during build phase. */
	public enum InterferenceMergeDomain {
		/** Use the same domain as the main analysis (default). */
		SAME_AS_ANALYSIS,
		/** Use OctagonDomain for interference merging (may preserve relational guards better). */
		OCTAGON
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}

	public ThreadModularSifaSettings(final boolean useGhostLocations,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final int outerWideningThreshold, final int innerWideningThreshold) {
		this(useGhostLocations ? LocationTrackingMode.GHOST_VARIABLES : LocationTrackingMode.NONE,
				locationAbstractionType, interferenceType, InterferenceRepresentation.RELATIONAL_LIGHT,
				outerWideningThreshold, innerWideningThreshold, true, InterferenceMergeDomain.SAME_AS_ANALYSIS);
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final int outerWideningThreshold, final int innerWideningThreshold, final boolean joinPrecision) {
		this(locationTrackingMode, locationAbstractionType, interferenceType, InterferenceRepresentation.RELATIONAL_LIGHT,
				outerWideningThreshold, innerWideningThreshold, joinPrecision,
				InterferenceMergeDomain.SAME_AS_ANALYSIS);
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType, final InterferenceType interferenceType,
			final InterferenceRepresentation interferenceRepresentation, final int outerWideningThreshold,
			final int innerWideningThreshold, final boolean joinPrecision) {
		this(locationTrackingMode, locationAbstractionType, interferenceType, interferenceRepresentation,
				outerWideningThreshold, innerWideningThreshold, joinPrecision,
				InterferenceMergeDomain.SAME_AS_ANALYSIS);
	}
}
