package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

/**
 * Represents a generic witness type in a YAML-based witness file.
 * 
 * @author Manuel Bentele
 */
public abstract class WitnessEntry {

	private final String mName;
	private final Metadata mMetadata;

	public WitnessEntry(final String name, final Metadata metadata) {
		mName = name;
		mMetadata = metadata;
	}

	public String getName() {
		return mName;
	}

	public Metadata getMetadata() {
		return mMetadata;
	}

	@Override
	public String toString() {
		return getName();
	}

	@Override
	public int hashCode() {
		return getName().hashCode();
	}
}
