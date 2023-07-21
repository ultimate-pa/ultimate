package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class LocationInvariant extends WitnessEntry {

	/**
	 * Witness entry name of the YAML witness format.
	 */
	public static final String NAME = "location_invariant";

	private final Location mLocation;
	private final Invariant mInvariant;

	public LocationInvariant(final Metadata metadata, final Location location, final Invariant invariant) {
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

	@Override
	public String toString() {
		return getClass().getSimpleName() + " @ " + mLocation + ": " + mInvariant;
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("entry_type", NAME).add("metadata", mMetadata.toYaml())
				.add("location", mLocation.toYaml()).add(NAME, mInvariant.toYaml()).build();
	}
}
