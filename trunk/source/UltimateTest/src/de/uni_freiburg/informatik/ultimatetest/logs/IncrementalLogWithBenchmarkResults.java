/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimatetest.logs;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Incremental log in which for each test the BenchmarkResults are shown.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class IncrementalLogWithBenchmarkResults extends DefaultIncrementalLogfile {

	public IncrementalLogWithBenchmarkResults(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	@Override
	public void addEntryPreStart(final UltimateRunDefinition runDef, final ILogger testLogger) {
		writeToFile(runDef.getInputFileNames() + CoreUtil.getPlatformLineSeparator(), testLogger);
	}

	@Override
	public void addEntryPostCompletion(final UltimateRunDefinition runDef, final TestResult result, final String resultCategory,
			final String resultMessage, final IUltimateServiceProvider services, final ILogger testLogger) {
		final String indent = "\t";
		final String lineSeparator = System.getProperty("line.separator");
		Entry sum = null;
		if (services != null) {
			sum = new Entry(result, resultMessage, runDef, services.getResultService());
		} else {
			sum = new Entry(result, resultMessage, runDef, null);
		}

		writeToFile(sum.toLogString(indent, lineSeparator).append(CoreUtil.getPlatformLineSeparator()).toString(),
				testLogger);
	}

	private class Entry {

		private final TestResult mThreeValuedResult;
		private final String mMessage;
		private final UltimateRunDefinition mUltimateRunDefinition;
		private final List<String> mFlattenedBenchmarkResults;

		public Entry(final TestResult threeValuedResult, final String message, final UltimateRunDefinition ultimateRunDefinition,
				final IResultService resultService) {
			super();
			mThreeValuedResult = threeValuedResult;
			mMessage = message;
			mUltimateRunDefinition = ultimateRunDefinition;
			mFlattenedBenchmarkResults = new ArrayList<>();
			if (resultService != null) {
				interpretUltimateResults(resultService);
			}
		}

		private void interpretUltimateResults(final IResultService resultService) {

			for (final IResult result : ResultUtil.filterResults(resultService.getResults(), BenchmarkResult.class)) {
				final StringBuilder sb = new StringBuilder();
				sb.append(result.getPlugin()).append(": ").append(result.getShortDescription()).append(": ").append(
						CoreUtil.flatten(result.getLongDescription(), " # "));
				mFlattenedBenchmarkResults.add(sb.toString());
			}
		}

		public StringBuilder toLogString(final String indent, final String lineSeparator) {
			final StringBuilder sb = new StringBuilder();

			sb.append(indent).append(mUltimateRunDefinition.getSettings()).append(",")
					.append(mUltimateRunDefinition.getToolchain()).append(lineSeparator);
			sb.append(indent).append("Test result: ").append(mThreeValuedResult).append(lineSeparator);
			sb.append(indent).append("Message:     ").append(CoreUtil.flatten(mMessage, " # ")).append(lineSeparator);
			if (mFlattenedBenchmarkResults.size() > 0) {
				sb.append(indent).append("Benchmarks:").append(lineSeparator);
				for (final String s : mFlattenedBenchmarkResults) {
					sb.append(indent).append(indent).append(s).append(lineSeparator);
				}
			}
			return sb;
		}

	}

}
