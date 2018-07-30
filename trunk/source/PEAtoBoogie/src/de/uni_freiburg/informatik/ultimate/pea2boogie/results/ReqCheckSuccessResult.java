package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

public final class ReqCheckSuccessResult<E extends IElement> extends AbstractResultAtElement<E> {

	private final ReqCheck mReqCheck;

	public ReqCheckSuccessResult(final E element, final String plugin,
			final IBacktranslationService translatorSequence) {
		super(element, plugin, translatorSequence);
		mReqCheck = (ReqCheck) ResultUtil.getCheckedSpecification(element);
	}

	@Override
	public String getShortDescription() {
		return mReqCheck.getPositiveMessage();
	}

	@Override
	public String getLongDescription() {
		return mReqCheck.getPositiveMessage();
	}

	public ReqCheck getCheck() {
		return mReqCheck;
	}
}