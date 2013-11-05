package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.result.IResult;

public class SVCOMP14TestSummary extends TestSummary {

	private HashMap<String, Summary> mSuccess;
	private HashMap<String, Summary> mUnknown;
	private HashMap<String, Summary> mFailure;

	private int mCount;

	private String mCategoryName;
	private String mLogFilePath;

	SVCOMP14TestSummary(String categoryName, String logFilePath) {
		mSuccess = new HashMap<String, Summary>();
		mFailure = new HashMap<String, Summary>();
		mUnknown = new HashMap<String, Summary>();
		mCategoryName = categoryName;
		mLogFilePath = logFilePath;
	}

	@Override
	String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append(mCategoryName)
				.append(" #################").append("\n");

		sb.append(getSummaryLog(mSuccess, "SUCCESSFUL TESTS"));
		int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(mUnknown, "UNKNOWN TESTS"));
		int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(mFailure, "FAILED TESTS"));
		int fail = mCount;
		total = total + mCount;
		sb.append("\n");
		sb.append("====== SUMMARY for ").append(mCategoryName)
				.append(" ======").append("\n");
		sb.append("Success:\t" + success).append("\n");
		sb.append("Unknown:\t" + unknown).append("\n");
		sb.append("Failures:\t" + fail).append("\n");
		sb.append("Total:\t\t" + total);
		return sb.toString();
	}
	
	@Override
	File getSummaryLogFile() {
		return new File(mLogFilePath);
	}

	private String getSummaryLog(HashMap<String, Summary> map, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append("\n");
		for (Entry<String, Summary> entry : map.entrySet()) {
			sb.append("\t").append(entry.getKey()).append("\n");

			for (Entry<String, String> fileMsgPair : entry.getValue().mFileMessage
					.entrySet()) {
				sb.append("\t\t").append(fileMsgPair.getKey()).append(": ")
						.append(fileMsgPair.getValue()).append("\n");
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ")
					.append(entry.getValue().count).append("\n");
			sb.append("\t--------").append("\n");
			mCount = mCount + entry.getValue().count;
		}
		sb.append("Count: ").append(mCount);
		sb.append("\n\n");
		return sb.toString();
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

	void addFail(IResult result, String filename, String message) {
		add(getSummary(mFailure, result), filename, message);
	}

	void addUnknown(IResult result, String filename, String message) {
		add(getSummary(mUnknown, result), filename, message);
	}

	void addSuccess(IResult result, String filename, String message) {
		add(getSummary(mSuccess, result), filename, message);
	}

	private void add(Summary s, String filename, String message) {
		s.count++;
		s.mFileMessage.put(filename, message);
	}

	private class Summary {

		private Summary() {
			mFileMessage = new HashMap<String, String>();
		}

		int count;
		HashMap<String, String> mFileMessage;
	}
}
