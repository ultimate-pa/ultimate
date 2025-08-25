package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;
import java.util.List;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifRun implements Serializable {

	@SerializedName("tool")
	private final SarifTool mTool;

	@SerializedName("results")
	private final List<SarifResult> mResults;

	public SarifRun(final SarifTool tool, final List<SarifResult> results) {
		mTool = tool;
		mResults = results;
	}

}
