package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class WitnessResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithTrace {

	private final CounterExampleResult<ELEM, TE, E> mCEXResult;
	private final String mWitness;
	private final boolean mIsVerified;

	public WitnessResult(CounterExampleResult<ELEM, TE, E> cexRes, String witness, boolean isVerified) {
		super(cexRes.getElement(), cexRes.getPlugin(), cexRes.m_TranslatorSequence);
		mCEXResult = cexRes;
		mWitness = witness;
		mIsVerified = isVerified;
	}

	@Override
	public String getShortDescription() {
		if (!isEmpty()) {
			if (isVerified()) {
				return "Verified witness for: " + mCEXResult.getShortDescription();
			} else {
				return "Witness verification failed for: " + mCEXResult.getShortDescription();
			}

		} else {
			return "No witness for: " + mCEXResult.getShortDescription();
		}

	}

	@Override
	public String getLongDescription() {
		if (!isEmpty()) {
			StringBuilder sb = new StringBuilder();
			sb.append(getShortDescription());
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append(mWitness);
			return sb.toString();
		} else {
			return "No witness for: " + mCEXResult.getLongDescription();
		}
	}

	@Override
	public List<ILocation> getFailurePath() {
		return mCEXResult.getFailurePath();
	}

	public boolean isVerified() {
		return mIsVerified;
	}

	public boolean isEmpty() {
		return mWitness == null;
	}

}
