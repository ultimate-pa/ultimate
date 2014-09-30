package de.uni_freiburg.informatik.ultimatetest.decider;


public abstract class TestResultDecider implements ITestResultDecider {

	private String mResultCategory;
	private String mResultMessage;
	
	public TestResultDecider() {
		mResultCategory = null;
		mResultMessage = null;
	}

	@Override
	public String getResultMessage() {
		return mResultMessage;
	}

	@Override
	public String getResultCategory() {
		return mResultCategory;
	}

	@Override
	public boolean getJUnitSuccess(TestResult actualResult) {
		switch (actualResult) {
		case SUCCESS:
			return true;
		case FAIL:
		case UNKNOWN:
			return false;
		default:
			return false;
		}

	}

	protected void setResultMessage(String resultMessage) {
		mResultMessage = resultMessage;
	}

	protected void setResultCategory(String resultCategory) {
		mResultCategory = resultCategory;
	}

}
