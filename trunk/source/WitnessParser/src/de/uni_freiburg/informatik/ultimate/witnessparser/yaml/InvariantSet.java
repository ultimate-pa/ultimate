package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class InvariantSet extends WitnessEntry {
	private final List<WitnessSetEntry> mContent;
	private static final String NAME = "invariant_set";

	public InvariantSet(final Metadata metadata, final List<WitnessSetEntry> content) {
		super(NAME, metadata);
		mContent = content;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("entry_type", NAME);
		result.put("metadata", mMetadata.toMap());
		result.put("content", mContent.stream().map(WitnessSetEntry::toMap).collect(Collectors.toList()));
		return result;
	}
}
