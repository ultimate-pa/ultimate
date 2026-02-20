package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceMergeMode interferenceMergeMode,
		InterferenceType interferenceType, QuantifierEliminationMode quantifierEliminationMode,
		int outerWideningThreshold, int innerWideningThreshold) {

	public static final int DEFAULT_OUTER_WIDENING_THRESHOLD = 2;
	public static final int DEFAULT_INNER_WIDENING_THRESHOLD = 2;

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	public enum InterferenceMergeMode {
		JOIN, OR
	}

	public enum InterferenceType {
		PER_THREAD, PER_ABSTRACT_LOCATION, PER_THREAD_JOINED_ABSTRACT_LOCATIONS
	}

	public enum QuantifierEliminationMode {
		LIGHT, STRONG
	}

	public ThreadModularSifaSettings {
		if (locationTrackingMode == null) {
			locationTrackingMode = LocationTrackingMode.GHOST_VARIABLES;
		}
		if (interferenceMergeMode == null) {
			interferenceMergeMode = InterferenceMergeMode.JOIN;
		}
		if (interferenceType == null) {
			interferenceType = InterferenceType.PER_ABSTRACT_LOCATION;
		}
		if (quantifierEliminationMode == null) {
			quantifierEliminationMode = QuantifierEliminationMode.LIGHT;
		}
		if (outerWideningThreshold < 1) {
			outerWideningThreshold = DEFAULT_OUTER_WIDENING_THRESHOLD;
		}
		if (innerWideningThreshold < 1) {
			innerWideningThreshold = DEFAULT_INNER_WIDENING_THRESHOLD;
		}
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType) {
		this(locationTrackingMode, locationAbstractionType, InterferenceMergeMode.JOIN,
				InterferenceType.PER_ABSTRACT_LOCATION, QuantifierEliminationMode.LIGHT,
				DEFAULT_OUTER_WIDENING_THRESHOLD, DEFAULT_INNER_WIDENING_THRESHOLD);
	}

	public ThreadModularSifaSettings(final LocationTrackingMode locationTrackingMode,
			final LocationAbstractionType locationAbstractionType, final InterferenceMergeMode interferenceMergeMode,
			final InterferenceType interferenceType, final int outerWideningThreshold,
			final int innerWideningThreshold) {
		this(locationTrackingMode, locationAbstractionType, interferenceMergeMode, interferenceType,
				QuantifierEliminationMode.LIGHT, outerWideningThreshold, innerWideningThreshold);
	}

	public ThreadModularSifaSettings(final boolean useGhostLocations,
			final LocationAbstractionType locationAbstractionType, final InterferenceMergeMode interferenceMergeMode,
			final InterferenceType interferenceType, final QuantifierEliminationMode quantifierEliminationMode,
			final int outerWideningThreshold, final int innerWideningThreshold) {
		this(useGhostLocations ? LocationTrackingMode.GHOST_VARIABLES : LocationTrackingMode.NONE,
				locationAbstractionType, interferenceMergeMode, interferenceType, quantifierEliminationMode,
				outerWideningThreshold, innerWideningThreshold);
	}
}
