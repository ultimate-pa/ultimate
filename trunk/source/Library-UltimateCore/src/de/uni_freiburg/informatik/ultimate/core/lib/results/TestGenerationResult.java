package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public class TestGenerationResult implements IResult {

	protected final String mPlugin;
	boolean mUnproven = false;

	public TestGenerationResult(final String plugin, final boolean unproven) {
		mPlugin = plugin;
		mUnproven = unproven;
	}

	@Override
	public final String getPlugin() {
		return mPlugin;
	}

	@Override
	public String getShortDescription() {
		if (mUnproven) {
			return "Unproven - TestGeneration";
		}
		return "TestGeneration";
	}

	@Override
	public String getLongDescription() {
		if (mUnproven) {
			return "Unproven - TestGeneration";
		}
		return "TestGeneration";
	}
}