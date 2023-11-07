package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class InvariantSet extends WitnessEntry {
	public static final String NAME = "invariant_set";

	private final List<InvariantSetEntry> mContent;

	public InvariantSet(final Metadata metadata, final List<InvariantSetEntry> content) {
		super(NAME, metadata);
		mContent = content;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("entry_type", NAME);
		result.put("metadata", mMetadata.toMap());
		result.put("content", mContent.stream().map(x -> Map.of("invariant", x.toMap())).collect(Collectors.toList()));
		return result;
	}

}
