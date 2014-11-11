package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result that reports that a nonterminating execution for a lasso shaped
 * sequence of statements has been found.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class NonterminatingLassoResult<ELEM extends IElement, TE extends IElement, EXP extends IElement> extends
		AbstractResultAtElement<ELEM> implements IResultWithInfiniteLassoTrace<TE, EXP> {

	protected final IProgramExecution<TE, EXP> mStem;
	protected final IProgramExecution<TE, EXP> mLoop;

	public NonterminatingLassoResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, EXP> stem, IProgramExecution<TE, EXP> loop, ILocation location) {
		super(position, plugin, translatorSequence);
		mStem = stem;
		mLoop = loop;
	}

	@Override
	public String getShortDescription() {
		return "Nonterminating execution";
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Found a nonterminating execution for the following lasso shaped sequence of statements.");
		sb.append(System.getProperty("line.separator"));
		sb.append("Stem:");
		sb.append(System.getProperty("line.separator"));
		sb.append(mTranslatorSequence.translateProgramExecution(mStem));
		sb.append("Loop:");
		sb.append(System.getProperty("line.separator"));
		sb.append(mTranslatorSequence.translateProgramExecution(mLoop));
		sb.append("End of lasso representation.");
		return sb.toString();
	}

	@Override
	public IProgramExecution<TE, EXP> getStem() {
		return mStem;
	}

	@Override
	public IProgramExecution<TE, EXP> getLasso() {
		return mLoop;
	}
}
