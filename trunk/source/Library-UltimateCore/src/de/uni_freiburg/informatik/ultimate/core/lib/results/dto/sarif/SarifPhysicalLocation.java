package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifPhysicalLocation implements Serializable {

	@SerializedName("artifactLocation")
	private final SarifArtifactLocation mArtifactLocation;

	@SerializedName("region")
	private final SarifRegion mRegion;

	public SarifPhysicalLocation(final SarifArtifactLocation artifactLocation, final SarifRegion region) {
		mArtifactLocation = artifactLocation;
		mRegion = region;
	}

}
