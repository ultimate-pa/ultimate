package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifDriver implements Serializable {

	@SerializedName("name")
	private final String mName;

	public SarifDriver(final String name) {
		mName = name;
	}

	public String getName() {
		return mName;
	}

}
