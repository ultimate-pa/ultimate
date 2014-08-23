package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.io.File;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;

public class SVCOMP14TestSummary extends TestSummary {

	private int mCount;

	private String mCategoryName;

	public SVCOMP14TestSummary(String categoryName, Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mCategoryName = categoryName;
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return this.getClass().getSimpleName();
	}
	
	@Override
	public String getFilenameExtension() {
		return ".log";
	}

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append(mCategoryName)
				.append(" #################").append("\n");

		sb.append(getSummaryLog(getSummaryMap(TestResult.SUCCESS), "SUCCESSFUL TESTS"));
		int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(getSummaryMap(TestResult.UNKNOWN), "UNKNOWN TESTS"));
		int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(getSummaryMap(TestResult.FAIL), "FAILED TESTS"));
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

	private String getSummaryLog(Map<String, Summary> map, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append("\n");
		for (Entry<String, Summary> entry : map.entrySet()) {
			sb.append("\t").append(entry.getKey()).append("\n");

			for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage()
					.entrySet()) {
				sb.append("\t\t").append(fileMsgPair.getKey()).append(": ")
						.append(fileMsgPair.getValue()).append("\n");
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ")
					.append(entry.getValue().getCount()).append("\n");
			sb.append("\t--------").append("\n");
			mCount = mCount + entry.getValue().getCount();
		}
		sb.append("Count: ").append(mCount);
		sb.append("\n\n");
		return sb.toString();
	}


}
