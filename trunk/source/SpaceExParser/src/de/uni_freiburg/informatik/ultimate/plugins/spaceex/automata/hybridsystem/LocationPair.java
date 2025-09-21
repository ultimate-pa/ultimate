package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

public class LocationPair {
	private final Location mLocation1;
	private final Location mLocation2;

	public LocationPair(final Location loc1, final Location loc2) {
		mLocation1 = loc1;
		mLocation2 = loc2;
	}

	public Location getLocation1() {
		return mLocation1;
	}

	public Location getLocation2() {
		return mLocation2;
	}

	@Override
	public String toString() {
		return mLocation1.toString() + "," + mLocation2.toString();
	}

}
