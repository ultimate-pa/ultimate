package de.uni_freiburg.informatik.ultimatetest;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.result.IResult;

public abstract class TestSummary implements ITestSummary{

	protected HashMap<String, Summary> mSuccess;
	protected HashMap<String, Summary> mUnknown;
	protected HashMap<String, Summary> mFailure;
	protected String mTestSuiteCanonicalName;

	public TestSummary( String testSuiteCanonicalName) {
		mSuccess = new HashMap<String, Summary>();
		mFailure = new HashMap<String, Summary>();
		mUnknown = new HashMap<String, Summary>();
		mTestSuiteCanonicalName =  testSuiteCanonicalName;
	}

	private Summary getSummary(HashMap<String, Summary> map, IResult result) {
		String typename = "NULL";
		if (result != null) {
			typename = result.getClass().getName();
		}
		Summary s = null;
		if (map.containsKey(typename)) {
			s = map.get(typename);
		} else {
			s = new Summary();
			map.put(typename, s);
		}
		return s;
	}

	public void addFail(IResult result, String filename, String message) {
		add(getSummary(mFailure, result), filename, message);
	}

	public void addUnknown(IResult result, String filename, String message) {
		add(getSummary(mUnknown, result), filename, message);
	}

	public void addSuccess(IResult result, String filename, String message) {
		add(getSummary(mSuccess, result), filename, message);
	}

	private void add(Summary s, String filename, String message) {
		s.setCount(s.getCount() + 1);
		s.getFileToMessage().put(filename, message);
	}
	
	@Override
	public String getTestSuiteCanonicalName() {
		return mTestSuiteCanonicalName;
	}
	
	public class Summary {

		private int mCount;
		private HashMap<String, String> mFileToMessage;
		
		private Summary() {
			mFileToMessage = new HashMap<String, String>();
		}

		public int getCount() {
			return mCount;
		}
		public void setCount(int count) {
			this.mCount = count;
		}

		public HashMap<String, String> getFileToMessage() {
			return mFileToMessage;
		}


	}


}