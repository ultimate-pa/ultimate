/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationTestCsvWriter {

	private String mFilePath;
	private final SimpleCsvProvider<String> mCsv;
	private final Triple<PrintWriter, BufferedWriter, FileWriter> mPrintWriter;
	private boolean mPrinted;
	private long mCurrentEliminationStartTime;
	private String[] mCurrentEliminationData;

	public QuantifierEliminationTestCsvWriter(final String testfileId) {
		final List<String> list =
				Arrays.asList(new String[] { "TestId", "InputTreesize", "OutputTreesize", "Runtime" });
		mCsv = new SimpleCsvProvider<>(list);
		final String workingDirectory = System.getProperty("user.dir");
		mPrintWriter = prepareFile(workingDirectory, testfileId);
	}

	public void reportEliminationBegin(final Term eliminationInput) {
		final String testId = ReflectionUtil.getCallerMethodName(4);
		if (mCurrentEliminationData == null) {
			mCurrentEliminationData = new String[4];
			mCurrentEliminationData[0] = testId;
			long treesize = new DAGSize().treesize(eliminationInput);
			assert mCurrentEliminationData[1] == null;
			mCurrentEliminationData[1] = String.valueOf(treesize);
			mCurrentEliminationStartTime = System.nanoTime();
		} else {
			throw new AssertionError("Writing PQE benchmarks failed: old data");
		}
	}
	
	public void reportTestFinished() {
		if (mCurrentEliminationData == null) {
			// do nothing
		} else {
			// elimination was not successful
			final long duration = computeDurationMiliseconds(mCurrentEliminationStartTime);
			assert mCurrentEliminationData[3] == null;
			mCurrentEliminationData[3] = String.valueOf(duration);
			mCsv.addRow(Arrays.asList(mCurrentEliminationData));
			mCurrentEliminationData = null;
		}
	}

	public void reportEliminationSuccess(final Term eliminationOutput) {
		final String testId = ReflectionUtil.getCallerMethodName(4);
		if (testId.equals(mCurrentEliminationData[0])) {
			long treesize = new DAGSize().treesize(eliminationOutput);
			assert mCurrentEliminationData[2] == null;
			mCurrentEliminationData[2] = String.valueOf(treesize);
			final long duration = computeDurationMiliseconds(mCurrentEliminationStartTime);
			assert mCurrentEliminationData[3] == null;
			mCurrentEliminationData[3] = String.valueOf(duration);
			mCsv.addRow(Arrays.asList(mCurrentEliminationData));
			mCurrentEliminationData = null;
		} else {
			throw new AssertionError("Writing PQE benchmarks failed: wrong ID");
		}
	}

	private long computeDurationMiliseconds(final long startTimeInNanoseconds) {
		final long durationNanoseconds = System.nanoTime() - startTimeInNanoseconds;
		return durationNanoseconds / 1000000;
	}

	public void writeCsv() throws IOException {
		if (mPrinted) {
			throw new AssertionError("Writing PQE benchmarks failed: must not print same csv twice");
		}
		mPrintWriter.getFirst().print(mCsv.toCsv(null, "\t", true));
		mPrintWriter.getFirst().flush();
		mPrintWriter.getSecond().flush();
		mPrintWriter.getThird().flush();
		System.out.println("Written .csv to file " + mFilePath);

		mPrintWriter.getFirst().close();
		mPrintWriter.getSecond().close();
		mPrintWriter.getThird().close();
		mPrinted = true;
	}

	private Triple<PrintWriter, BufferedWriter, FileWriter> prepareFile(final String directory,
			final String testfileId) {
		mFilePath = directory + File.separator + getDateTime() + testfileId + ".csv";
		final File file = new File(mFilePath);
		try {
			final FileWriter fileWriter = new FileWriter(file);
			final BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
			final PrintWriter printWriter = new PrintWriter(bufferedWriter);
			return new Triple<>(printWriter, bufferedWriter, fileWriter);
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	private static String getDateTime() {
		final DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
		final Date date = new Date();
		return dateFormat.format(date);
	}
}
