package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public class TestGenerationResult implements IResult {

	protected final String mPlugin;

	public TestGenerationResult(final String plugin) {
		mPlugin = plugin;
	}

	@Override
	public final String getPlugin() {
		return mPlugin;
	}

	@Override
	public String getShortDescription() {
		return "TestGeneration";
	}

	@Override
	public String getLongDescription() {
		return "TestGeneration";
	}
}