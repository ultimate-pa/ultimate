/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.reporting.OldTestSummary;

public class SVCOMP14TestSummary extends OldTestSummary {

	private int mCount;

	private String mCategoryName;

	public SVCOMP14TestSummary(String categoryName, Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mCategoryName = categoryName;
	}
	
	@Override
	public String getDescriptiveLogName() {
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
