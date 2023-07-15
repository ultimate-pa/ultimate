package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

public class LoopInvariant extends WitnessEntry {

	/**
	 * Witness entry name of the YAML witness format.
	 */
	public static final String NAME = "loop_invariant";

	private final Location mLocation;
	private final Invariant mInvariant;

	public LoopInvariant(final Metadata metadata, final Location location, final Invariant invariant) {
		super(NAME, metadata);
		mLocation = location;
		mInvariant = invariant;
	}

	public Location getLocation() {
		return mLocation;
	}

	public Invariant getInvariant() {
		return mInvariant;
	}
}
