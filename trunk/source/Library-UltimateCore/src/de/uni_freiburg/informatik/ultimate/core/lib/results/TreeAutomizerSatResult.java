package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * If TreeAutomizer finds out "SAT", it will report this result.
 * In the future this may contain a model.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TreeAutomizerSatResult implements IResult {

	private String mLongDescription;
	private String mShortDescription;
	private String mPlugin;

	public TreeAutomizerSatResult(String plugin, String shortDescription, String longDescription) {
		mPlugin = plugin;
		mShortDescription = shortDescription;
		mLongDescription = longDescription;
	}

	@Override
	public String getPlugin() {
		return mPlugin;
	}

	@Override
	public String getShortDescription() {
		return mShortDescription;
	}

	@Override
	public String getLongDescription() {
		return mLongDescription;
	}
}
