package de.uni_freiburg.informatik.ultimatetest.summary;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;

public abstract class OldTestSummary implements ITestSummary {

	private HashMap<String, Summary> mSuccess;
	private HashMap<String, Summary> mUnknown;
	private HashMap<String, Summary> mFailure;
	private Class<? extends UltimateTestSuite> m_UltimateTestSuite;

	public OldTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		mSuccess = new HashMap<String, Summary>();
		mFailure = new HashMap<String, Summary>();
		mUnknown = new HashMap<String, Summary>();
		m_UltimateTestSuite = ultimateTestSuite;
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category, String message, String testname, IResultService resultService) {
		switch (threeValuedResult) {
		case FAIL:
			add(getSummary(mFailure, category), ultimateRunDefinition, message);
			break;
		case SUCCESS:
			add(getSummary(mSuccess, category), ultimateRunDefinition, message);
			break;
		case UNKNOWN:
			add(getSummary(mUnknown, category), ultimateRunDefinition, message);
			break;
		default:
			throw new IllegalArgumentException("TestResult 'actualResult' has an unknown value");
		}
	}
	
	

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return m_UltimateTestSuite;
	}

	public StringBuilder generateCanonicalSummary() {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		Map<TestResult, Integer> count = new HashMap<>();

		for (TestResult result : TestResult.class.getEnumConstants()) {
			int resultCategoryCount = 0;
			sb.append("===== ").append(result.toString()).append(" =====").append(lineSeparator);

			for (Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				sb.append("\t").append(entry.getKey()).append(lineSeparator);

				for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
					sb.append("\t\t").append(fileMsgPair.getKey());
					String customMessage = fileMsgPair.getValue();
					if (customMessage != null && !customMessage.isEmpty()) {
						sb.append(": ").append(customMessage);
					}
					sb.append(lineSeparator);
				}

				sb.append("\tCount for ").append(entry.getKey()).append(": ").append(entry.getValue().getCount())
						.append(lineSeparator);
				sb.append("\t--------").append(lineSeparator).append(lineSeparator);
				
				resultCategoryCount = resultCategoryCount + entry.getValue().getCount();
			}
			sb.append("Count: ").append(resultCategoryCount);
			sb.append(lineSeparator).append(lineSeparator);

			count.put(result, resultCategoryCount);

		}

		int total = 0;
		for (TestResult result : TestResult.class.getEnumConstants()) {
			int current = count.get(result);
			sb.append(result.toString()).append(": ").append(current).append(lineSeparator);
			total += current;
		}
		sb.append("Total: ").append(total).append(lineSeparator);
		return sb;
	}

	protected Map<String, Summary> getSummaryMap(TestResult result) {
		switch (result) {
		case FAIL:
			return mFailure;
		case SUCCESS:
			return mSuccess;
		case UNKNOWN:
			return mUnknown;
		default:
			throw new IllegalArgumentException("TestResult 'result' has an unknown value");
		}
	}

	private Summary getSummary(HashMap<String, Summary> map, String result) {
		String typename = "NULL";
		if (result != null) {
			typename = result;
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

	private void add(Summary s, UltimateRunDefinition ultimateRunDefinition, String message) {
		s.setCount(s.getCount() + 1);
		s.getFileToMessage().put(ultimateRunDefinition.getInput().getAbsolutePath(), message);
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