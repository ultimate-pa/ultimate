package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import com.google.gson.annotations.SerializedName;

public final class Result {

	@SerializedName("description")
	private final Description mDescription;

	@SerializedName("data")
	private final Object mData;

	public Result(final Description description, final Object data) {
		mDescription = description;
		mData = data;
	}

	public Description getDescription() {
		return mDescription;
	}

	public Object getData() {
		return mData;
	}
}
