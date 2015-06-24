package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

public class SignDomainValue implements IEvaluationResult<SignDomainValue.Values> {

	private Values mValue;

	public enum Values {
		POSITIVE, NEGATIVE, ZERO, BOTTOM, TOP,
	}

	protected SignDomainValue() {
		mValue = Values.TOP;
	}
	
	protected SignDomainValue(Values value) {
		mValue = value;
	}

	@Override
	public Values getResult() {
		return mValue;
	}

	@Override
	public void setResult(SignDomainValue.Values value) {
		mValue = value;
	}

}