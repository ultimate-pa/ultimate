/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.reporting;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;

/**
 * @deprecated Use {@link NewTestSummary} instead.
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
@Deprecated
public abstract class OldTestSummary implements ITestSummary {

	private final HashMap<String, Summary> mSuccess;
	private final HashMap<String, Summary> mUnknown;
	private final HashMap<String, Summary> mFailure;
	private final Class<? extends UltimateTestSuite> mUltimateTestSuite;

	public OldTestSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		mSuccess = new HashMap<String, Summary>();
		mFailure = new HashMap<String, Summary>();
		mUnknown = new HashMap<String, Summary>();
		mUltimateTestSuite = ultimateTestSuite;
	}

	@Override
	public void addResult(final UltimateRunDefinition ultimateRunDefinition, final TestResult threeValuedResult, final String category,
			final String message, final String testname, final IResultService resultService) {
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
		return mUltimateTestSuite;
	}

	public StringBuilder generateCanonicalSummary() {
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		final Map<TestResult, Integer> count = new HashMap<>();

		for (final TestResult result : TestResult.class.getEnumConstants()) {
			int resultCategoryCount = 0;
			sb.append("===== ").append(result.toString()).append(" =====").append(lineSeparator);

			for (final Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				sb.append("\t").append(entry.getKey()).append(lineSeparator);

				for (final Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
					sb.append("\t\t").append(fileMsgPair.getKey());
					final String customMessage = fileMsgPair.getValue();
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
		for (final TestResult result : TestResult.class.getEnumConstants()) {
			final int current = count.get(result);
			sb.append(result.toString()).append(": ").append(current).append(lineSeparator);
			total += current;
		}
		sb.append("Total: ").append(total).append(lineSeparator);
		return sb;
	}

	protected Map<String, Summary> getSummaryMap(final TestResult result) {
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

	private Summary getSummary(final HashMap<String, Summary> map, final String result) {
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

	private void add(final Summary s, final UltimateRunDefinition ultimateRunDefinition, final String message) {
		s.setCount(s.getCount() + 1);
		s.getFileToMessage().put(ultimateRunDefinition.getInputFileNames(), message);
	}

	public static final class Summary {

		private int mCount;
		private final HashMap<String, String> mFileToMessage;

		Summary() {
			mFileToMessage = new HashMap<String, String>();
		}

		public int getCount() {
			return mCount;
		}

		public void setCount(final int count) {
			mCount = count;
		}

		public HashMap<String, String> getFileToMessage() {
			return mFileToMessage;
		}

	}

}
