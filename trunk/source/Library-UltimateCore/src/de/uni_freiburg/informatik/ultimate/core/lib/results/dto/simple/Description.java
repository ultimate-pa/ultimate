package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import com.google.gson.annotations.SerializedName;

public final class Description {

	@SerializedName("short")
	private final String mShort;

	@SerializedName("long")
	private final String mLong;

	public Description(final String shortDesc, final String longDesc) {
		mShort = shortDesc;
		mLong = longDesc;
	}

	public String getShortDesc() {
		return mShort;
	}

	public String getLongDesc() {
		return mLong;
	}
}
