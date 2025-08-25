package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifLocation implements Serializable {

	@SerializedName("physicalLocaiton")
	private final SarifPhysicalLocation mPhysicalLocation;

	public SarifLocation(final SarifPhysicalLocation physicalLocation) {
		mPhysicalLocation = physicalLocation;
	}

}
