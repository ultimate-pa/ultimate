package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;
import java.util.List;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifDTO implements Serializable {

	@SerializedName("version")
	private static final String VERSION = "2.1.0";

	@SerializedName("$schema")
	private static final String SCHEMA = "https://json.schemastore.org/sarif-2.1.0-rtm.5.json";

	private final List<SarifRun> mRuns;

	public SarifDTO(final List<SarifRun> runs) {
		mRuns = runs;
	}

}
