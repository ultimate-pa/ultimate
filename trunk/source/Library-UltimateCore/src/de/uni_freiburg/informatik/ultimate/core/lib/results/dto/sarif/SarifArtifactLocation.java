package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifArtifactLocation implements Serializable {

	@SerializedName("uri")
	private final String mUri;

	public SarifArtifactLocation(final String uri) {
		mUri = uri;
	}

}
