package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness.IMapSerializable;

public class InvariantSetEntry implements IMapSerializable {
	private final String mType;
	private final Location mLocation;
	private final Map<String, Object> mOtherValues;

	public InvariantSetEntry(final String type, final Location location, final Map<String, Object> otherValues) {
		mType = type;
		mLocation = location;
		mOtherValues = otherValues;
	}

	public String getType() {
		return mType;
	}

	public Location getLocation() {
		return mLocation;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("type", mType);
		result.put("location", mLocation.toMap());
		result.putAll(mOtherValues);
		return result;
	}

}
