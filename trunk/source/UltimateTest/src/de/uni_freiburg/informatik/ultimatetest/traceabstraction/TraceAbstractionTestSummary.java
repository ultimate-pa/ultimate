package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.TestSummary.Summary;

public class TraceAbstractionTestSummary extends TestSummary {

	private int mCount;

	private String mLogFilePath;
	private String m_InterpolationType;
	private Map<Integer, Integer> testCase2Iterations;
	
	public TraceAbstractionTestSummary(String testSuiteCanonicalName, String logFilePath,
			String interpolationType) {
		super(testSuiteCanonicalName);
		mLogFilePath = logFilePath;
		mCount = 0;
		m_InterpolationType = interpolationType;
		testCase2Iterations = new HashMap<Integer, Integer>();
	}
	
	public void setIterationsOfTestCase(Integer testCase, Integer iterations) {
		testCase2Iterations.put(testCase, iterations);
	}
	
	@Override
	public String getSummaryLog() {

		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append(m_InterpolationType)
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
		sb.append("====== SUMMARY for ").append(m_InterpolationType)
				.append(" ======").append("\n");
		sb.append("Success:\t" + success).append("\n");
		sb.append("Unknown:\t" + unknown).append("\n");
		sb.append("Failures:\t" + fail).append("\n");
		sb.append("Total:\t\t" + total);
		for (int i = 0; i < testCase2Iterations.size(); i++) {
			sb.append("Iterations at testcase " + i + ":\t\t " + testCase2Iterations.get(new Integer(i)));
		}
		return sb.toString();
	
	}
	
	private String getSummaryLog(HashMap<String, Summary> map, String title) {
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


	@Override
	public File getSummaryLogFile() {
		return new File(mLogFilePath);
	}

}
