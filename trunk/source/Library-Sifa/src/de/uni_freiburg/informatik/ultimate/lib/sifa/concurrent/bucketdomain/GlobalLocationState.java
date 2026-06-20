package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.Map;

// One combination of assignments of abstract location values to thread IDs.
// UNKNOWN is the fallsback if locations couldnt be determined, or all are just true
public record GlobalLocationState(Map<String, Integer> locs) {
	static final GlobalLocationState UNKNOWN = new GlobalLocationState(Map.of());

	public GlobalLocationState {
		locs = Map.copyOf(locs);
	}
}
