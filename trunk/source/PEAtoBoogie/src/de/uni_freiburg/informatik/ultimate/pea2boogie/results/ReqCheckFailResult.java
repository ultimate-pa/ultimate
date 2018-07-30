package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

public final class ReqCheckFailResult<E extends IElement> extends AbstractResultAtElement<E> {

	private final ReqCheck mReqCheck;

	public ReqCheckFailResult(final E element, final String plugin, final IBacktranslationService translatorSequence) {
		super(element, plugin, translatorSequence);
		mReqCheck = (ReqCheck) ResultUtil.getCheckedSpecification(element);
	}

	@Override
	public String getShortDescription() {
		return mReqCheck.getNegativeMessage();
	}

	@Override
	public String getLongDescription() {
		return mReqCheck.getNegativeMessage();
	}

	public ReqCheck getCheck() {
		return mReqCheck;
	}

}