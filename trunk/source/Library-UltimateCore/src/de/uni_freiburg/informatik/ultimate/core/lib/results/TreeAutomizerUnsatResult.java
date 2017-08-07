package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * If TreeAutomizer finds out "UNSAT", it will report this result.
 * In the future this may contain a counterexample to SAT, i.e., a derivation tree that can be built in the input Horn
 * clause set.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TreeAutomizerUnsatResult implements IResult {
	
	private String mLongDescription;
	private String mShortDescription;
	private String mPlugin;

	public TreeAutomizerUnsatResult(String plugin, String shortDescription, String longDescription) {
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
