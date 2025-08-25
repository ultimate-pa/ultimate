package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifResult implements Serializable {

	@SerializedName("ruleId")
	private final String mRuleId;

	@SerializedName("message")
	private final SarifMessage mMessage;

	public SarifResult(final String ruleId, final SarifMessage message) {
		mRuleId = ruleId;
		mMessage = message;
	}

	public String getRuleId() {
		return mRuleId;
	}

	public SarifMessage getMessage() {
		return mMessage;
	}

}
