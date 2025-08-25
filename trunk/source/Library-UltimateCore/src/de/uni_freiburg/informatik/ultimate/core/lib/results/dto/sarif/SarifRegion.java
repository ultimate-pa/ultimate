package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifRegion implements Serializable {

	@SerializedName("startLine")
	private final int mStartLine;

	@SerializedName("startColumn")
	private final int mStartColumn;

	public SarifRegion(final int startLine, final int startColumn) {
		mStartLine = startLine;
		mStartColumn = startColumn;
	}

}
