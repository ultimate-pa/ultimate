package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import java.util.List;

import com.google.gson.annotations.SerializedName;

public final class Input {

	@SerializedName("files")
	private final List<String> mFiles;

	public Input(final List<String> files) {
		mFiles = files;
	}

	public List<String> getFiles() {
		return mFiles;
	}
}
