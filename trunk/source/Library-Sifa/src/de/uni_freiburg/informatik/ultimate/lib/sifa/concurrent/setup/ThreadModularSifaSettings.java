/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstractionType;

public record ThreadModularSifaSettings(LocationTrackingMode locationTrackingMode,
		LocationAbstractionType locationAbstractionType, InterferenceApplicatorType interferenceApplicatorType,
		int outerWideningThreshold, int innerWideningThreshold, boolean joinPrecision, boolean useBuckets,
		boolean locksetAwareInterference, boolean publishOnAcquire, boolean proofCheck, boolean resultPrint,
		int maxBuckets, int maxDisjunctsPerBucket) {

	public static final int DEFAULT_MAX_BUCKETS = 10;
	public static final int DEFAULT_MAX_DISJUNCTS_PER_BUCKET = 2;

	public enum LocationTrackingMode {
		GHOST_VARIABLES, NONE
	}

	public enum InterferenceApplicatorType {
		STRONGEST_POSTCONDITION, GUARDED_EXACT_UPDATE, POST_STATE
	}

	public boolean useGhostLocations() {
		return locationTrackingMode == LocationTrackingMode.GHOST_VARIABLES;
	}
}
