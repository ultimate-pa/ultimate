package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class WitnessResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithFiniteTrace<TE, E> {

	public static enum WitnessVerificationStatus {
		VERIFIED, UNVERIFIED, VERIFICATION_FAILED, INTERNAL_ERROR
	}

	private final CounterExampleResult<ELEM, TE, E> mCEXResult;
	private final String mWitness;
	private final WitnessVerificationStatus mVerificationStatus;

	public WitnessResult(CounterExampleResult<ELEM, TE, E> cexRes, String witness,
			WitnessVerificationStatus verificationStatus) {
		super(cexRes.getElement(), cexRes.getPlugin(), cexRes.mTranslatorSequence);
		mCEXResult = cexRes;
		mWitness = witness;
		mVerificationStatus = verificationStatus;
	}

	@Override
	public String getShortDescription() {
		if (isEmpty()) {
			return "No witness for: " + mCEXResult.getShortDescription();
		}

		switch (getVerificationStatus()) {
		case INTERNAL_ERROR:
			return "An error occured during witness verification for: " + mCEXResult.getShortDescription();
		case UNVERIFIED:
			return "Unverified witness for: " + mCEXResult.getShortDescription();
		case VERIFICATION_FAILED:
			return "Witness verification failed for: " + mCEXResult.getShortDescription();
		case VERIFIED:
			return "Verified witness for: " + mCEXResult.getShortDescription();
		default:
			throw new UnsupportedOperationException("Enum value " + getVerificationStatus() + " is unhandled");
		}
	}

	@Override
	public String getLongDescription() {
		return getShortDescription();
	}

	@Override
	public List<ILocation> getFailurePath() {
		return mCEXResult.getFailurePath();
	}

	public WitnessVerificationStatus getVerificationStatus() {
		return mVerificationStatus;
	}

	public boolean isEmpty() {
		return mWitness == null;
	}

	public CounterExampleResult<ELEM, TE, E> getCounterExampleResult() {
		return mCEXResult;
	}

	@Override
	public IProgramExecution<TE, E> getProgramExecution() {
		if (mCEXResult == null) {
			return null;
		}
		return mCEXResult.getProgramExecution();
	};

}
