package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

public enum TrackNumber {
	TRACK_ONE,
	TRACK_TWO;
	
	public boolean isOne() {
		return this == TRACK_ONE;
	}
	
	public boolean isTwo() {
		return this == TRACK_TWO;
	}
}
