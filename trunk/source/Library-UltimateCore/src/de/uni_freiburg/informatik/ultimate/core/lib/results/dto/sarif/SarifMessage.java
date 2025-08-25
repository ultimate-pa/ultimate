package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifMessage implements Serializable {
	@SerializedName("text")
	private final String mText;

	public SarifMessage(final String text) {
		mText = text;
	}

	public String getText() {
		return mText;
	}

}
