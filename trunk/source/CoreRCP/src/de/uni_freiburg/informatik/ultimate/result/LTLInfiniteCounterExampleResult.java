package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result that reports that a counter example for an LTL property was found and
 * that it is infinite.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class LTLInfiniteCounterExampleResult<ELEM extends IElement, TE extends IElement, E extends IElement> extends
		NonterminatingLassoResult<ELEM, TE, E> {

	private final String mLTLProperty;

	public LTLInfiniteCounterExampleResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, E> stem, IProgramExecution<TE, E> loop, ILocation location, String ltlproperty) {
		super(position, plugin, translatorSequence, stem, loop, location);
		mLTLProperty = ltlproperty;
	}

	@Override
	public String getShortDescription() {
		return "Violation of LTL property " + mLTLProperty;
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Found an infinite, lasso-shaped execution that violates the LTL property ");
		sb.append(mLTLProperty);
		sb.append(".");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("Stem:");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(mTranslatorSequence.translateProgramExecution(mStem));
		sb.append("Loop:");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(mTranslatorSequence.translateProgramExecution(mLoop));
		sb.append("End of lasso representation.");
		return sb.toString();
	}

}
