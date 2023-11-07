package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness.IMapSerializable;

public class InvariantSetEntry implements IMapSerializable {
	private final String mType;
	private final Location mLocation;
	private final String mValue;
	private final String mFormat;

	public InvariantSetEntry(final String type, final Location location, final String value, final String format) {
		mType = type;
		mLocation = location;
		mValue = value;
		mFormat = format;
	}

	public String getType() {
		return mType;
	}

	public Location getLocation() {
		return mLocation;
	}

	public String getValue() {
		return mValue;
	}

	public String getFormat() {
		return mFormat;
	}

	@Override
	public Map<String, Object> toMap() {
		final LinkedHashMap<String, Object> result = new LinkedHashMap<>();
		result.put("type", mType);
		result.put("location", mLocation.toMap());
		result.put("value", mValue);
		result.put("format", mFormat);
		return result;
	}

}
