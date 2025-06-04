package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import java.util.List;
import java.util.Map;

import com.google.gson.annotations.SerializedName;

public final class Config {

	@SerializedName("toolchain")
	private final List<String> mToolchainPlugins;

	@SerializedName("settings")
	private final Map<String, List<Setting>> mSettings;

	public Config(final List<String> toolchainPlugins, final Map<String, List<Setting>> settings) {
		mToolchainPlugins = toolchainPlugins;
		mSettings = settings;
	}

	public List<String> getToolchain() {
		return mToolchainPlugins;
	}

	public Map<String, List<Setting>> getSettings() {
		return mSettings;
	}
}
