package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class ReqCheckRedundancyResult<LOC extends IElement> extends ReqCheckFailResult<LOC> {

	private final String mReqName;
	private final String mRedundancySet;

	public ReqCheckRedundancyResult(final LOC element, final String plugin, final String reqName,
			final String redundancySet) {
		super(element, plugin);
		mReqName = reqName;
		mRedundancySet = redundancySet;
	}

	@Override
	public String getLongDescription() {
		return "Extracted redundancy set for requirement " + mReqName + ": " + mRedundancySet;
	}

}
