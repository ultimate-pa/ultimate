package de.uni_freiburg.informatik.ultimate.web.backend.dto;

import com.google.gson.annotations.SerializedName;

public class VersionResponse extends ApiResponse {

	private static final long serialVersionUID = 1L;

	@SerializedName("ultimate_version")
	private final String mUltimateVersion;

	public VersionResponse(final String version) {
		super();
		setStatusError();
		mUltimateVersion = version;
	}
}
