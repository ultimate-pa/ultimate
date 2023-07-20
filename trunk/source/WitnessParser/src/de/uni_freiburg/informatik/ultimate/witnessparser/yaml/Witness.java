package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;

public class Witness extends BasePayloadContainer {
	private static final long serialVersionUID = 2111530908758373549L;

	private final List<WitnessEntry> mEntries;

	public Witness(final List<WitnessEntry> entries) {
		mEntries = entries;
	}

	public List<WitnessEntry> getEntries() {
		return mEntries;
	}

	@Override
	public String toString() {
		return mEntries.toString();
	}
}
