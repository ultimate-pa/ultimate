package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SarifTool implements Serializable {

	@SerializedName("driver")
	private final SarifDriver mDriver;

	public SarifTool(final SarifDriver driver) {
		mDriver = driver;
	}

}
