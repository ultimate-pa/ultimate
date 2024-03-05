package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class EntrySet extends WitnessEntry {
	private final List<WitnessSetEntry> mContent;
	private final String mEntryType;

	public EntrySet(final Metadata metadata, final List<WitnessSetEntry> content) {
		super(metadata.getFormatVersion().getMajor() < 3 ? "invariant_set" : "entry_set", metadata);
		mContent = content;
		mEntryType = metadata.getFormatVersion().getMajor() < 3 ? "invariant_set" : "entry_set";
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("entry_type", mEntryType);
		result.put("metadata", mMetadata.toMap());
		result.put("content", mContent.stream().map(this::getMapForEntry).collect(Collectors.toList()));
		return result;
	}

	private Map<String, Object> getMapForEntry(final WitnessSetEntry x) {
		return mMetadata.getFormatVersion().getMajor() >= 3 ? x.toMap() : Map.of("invariant", x.toMap());
	}
}
