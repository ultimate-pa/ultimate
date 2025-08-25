package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;
import java.util.List;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifResult implements Serializable {

	@SerializedName("ruleId")
	private final String mRuleId;

	@SerializedName("message")
	private final SarifMessage mMessage;

	@SerializedName("locations")
	private final List<SarifLocation> mLocations;

	public SarifResult(final String ruleId, final SarifMessage message, final List<SarifLocation> locations) {
		mRuleId = ruleId;
		mMessage = message;
		mLocations = locations;
	}

}
