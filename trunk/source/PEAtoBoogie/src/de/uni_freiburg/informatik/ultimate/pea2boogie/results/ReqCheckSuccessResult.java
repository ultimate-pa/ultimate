package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public final class ReqCheckSuccessResult<E extends IElement> extends AbstractResultAtElement<E> {

	private final ReqCheck mReqCheck;

	public ReqCheckSuccessResult(final E element, final String plugin) {
		super(element, plugin);
		mReqCheck = (ReqCheck) Check.getAnnotation(element);
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