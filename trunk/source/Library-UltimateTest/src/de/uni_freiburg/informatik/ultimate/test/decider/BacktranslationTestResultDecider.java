/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.test.decider;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IPath;

import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExternalWitnessValidationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExternalWitnessValidationResult.WitnessVerificationStatus;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class BacktranslationTestResultDecider extends TestResultDecider {
	private final UltimateRunDefinition mRunDefinition;
	private final String mInputFilePath;

	public BacktranslationTestResultDecider(final UltimateRunDefinition runDefinition) {
		mRunDefinition = runDefinition;
		mInputFilePath = runDefinition.selectPrimaryInputFile().getAbsolutePath();
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {
		setResultCategory("");
		setResultMessage("");

		final ILogger log = services.getLoggingService().getLogger(BacktranslationTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<>();
		customMessages.add("Expecting results to not contain GenericResult \"Unhandled Backtranslation\" "
				+ ", ExceptionOrErrorResult or TypeErrorResult, "
				+ "and that there is a counter example result, and that the contained error trace "
				+ "matches the given one.");

		final List<CounterExampleResult<?, ?, ?>> cex = new ArrayList<>();
		final List<ExternalWitnessValidationResult> witnesses = new ArrayList<>();
		final IResultService resultService = services.getResultService();

		final List<IResult> results = resultService.getResults().entrySet().stream().flatMap(a -> a.getValue().stream())
				.collect(Collectors.toList());
		for (final IResult result : results) {
			if (result instanceof ExceptionOrErrorResult || result instanceof TypeErrorResult<?>
					|| result instanceof SyntaxErrorResult) {
				setCategoryAndMessageAndCustomMessage(result.getShortDescription(), customMessages);
				TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
				return TestResult.FAIL;
			} else if (result instanceof GenericResult) {
				final GenericResult genRes = (GenericResult) result;
				if (genRes.getShortDescription().equals("Unfinished Backtranslation")) {
					setResultCategory(result.getShortDescription());
					setResultMessage(result.getLongDescription());
					customMessages.add(result.getShortDescription() + ": " + result.getLongDescription());
					TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
					return TestResult.FAIL;
				}
			} else if (result instanceof CounterExampleResult<?, ?, ?>) {
				cex.add((CounterExampleResult<?, ?, ?>) result);
			} else if (result instanceof ExternalWitnessValidationResult) {
				witnesses.add((ExternalWitnessValidationResult) result);
			}
		}

		if (cex.isEmpty()) {
			setCategoryAndMessageAndCustomMessage("No counter example found", customMessages);
			TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
			return TestResult.FAIL;
		}
		if (cex.size() > 1) {
			setResultCategory("More than one counter example found");
			final String errorMsg = "There were " + cex.size() + " counter examples, but we expected only one";
			setResultMessage(errorMsg);
			customMessages.add(errorMsg);
			TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
			return TestResult.FAIL;
		}

		final List<ExternalWitnessValidationResult> witnessesWithCex = new ArrayList<>();
		for (final IResult result : cex) {
			final Optional<ExternalWitnessValidationResult> witness =
					witnesses.stream().filter(a -> a.getAffectedResult() == result).findAny();
			if (witness.isPresent()) {
				witnessesWithCex.add(witness.get());
			}
		}

		if (!witnessesWithCex.isEmpty()) {
			// we expect witness verification for .c files to succeed
			for (final ExternalWitnessValidationResult witness : witnessesWithCex) {
				if (witness.isEmpty()) {
					setResultCategory("Empty Witness");
					final String errorMsg = "The witness is empty: " + witness.getShortDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
					return TestResult.FAIL;
				} else if (witness.getExpectedVerificationStatus() == WitnessVerificationStatus.VERIFIED
						&& witness.getVerificationStatus() != WitnessVerificationStatus.VERIFIED) {
					setResultCategory("Witness failed to verify");
					final String errorMsg = "The witness failed to verify: " + witness.getLongDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
					return TestResult.FAIL;
				}
			}
		}

		// so far so good, now we compare the error path with the expected
		// error path
		boolean fail = false;
		String desiredCounterExample = null;
		try {
			desiredCounterExample = getDesiredCounterExample(mRunDefinition);
		} catch (final IOException e) {
			setResultCategory(e.getMessage());
			setResultMessage(e.toString());
			e.printStackTrace();
			TestUtil.logResults(log, mInputFilePath, true, customMessages, resultService);
			return TestResult.FAIL;
		}

		final String actualCounterExample = cex.get(0).getProgramExecutionAsString();
		if (desiredCounterExample == null) {
			setResultCategory("No .errorpath file for comparison");
			final String errorMsg = String.format("There is no .errorpath file for %s!", mInputFilePath);
			tryWritingActualResultToFile(actualCounterExample);
			setResultMessage(errorMsg);
			customMessages.add(errorMsg);
			fail = true;
		} else {
			final StringCounterexample desired = new StringCounterexample(desiredCounterExample);
			final StringCounterexample actual = new StringCounterexample(actualCounterExample);

			final Difference difference = desired.getFirstDifference(actual);

			fail = difference != null;

			if (fail) {
				tryWritingActualResultToFile(actualCounterExample);
				setCategoryAndMessageAndCustomMessage("Desired error trace does not match actual error trace.",
						customMessages);
				customMessages.add("Lengths: Desired=" + desired.mLines.size() + " Actual=" + actual.mLines.size());
				customMessages.addAll(difference.getCustomDifferenceMessage());
				customMessages
						.add("Desired error trace:" + CoreUtil.getPlatformLineSeparator() + desiredCounterExample);
				customMessages.add("Actual error trace:" + CoreUtil.getPlatformLineSeparator() + actualCounterExample);
			} else {
				setResultCategory("Success");
			}
		}
		TestUtil.logResults(log, mInputFilePath, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	private static String getDesiredCounterExample(final UltimateRunDefinition rundefinition) throws IOException {
		final File inputFile = rundefinition.selectPrimaryInputFile();
		final String inputDir = inputFile.getParentFile().getAbsolutePath();
		final String inputFileNameWithoutEnding = removeFileEnding(inputFile);
		final String settingsFileNameWithoutEnding = removeFileEnding(rundefinition.getSettings());
		final String toolchainFileNameWithoutEnding = removeFileEnding(rundefinition.getToolchain());

		// order some candidates which we would like, we take the first that
		// matches
		final List<File> candidates = new ArrayList<>();
		candidates.add(getDesiredCounterExampleCandidate(inputDir, inputFileNameWithoutEnding + "_"
				+ toolchainFileNameWithoutEnding + "_" + settingsFileNameWithoutEnding));
		candidates.add(getDesiredCounterExampleCandidate(inputDir,
				inputFileNameWithoutEnding + "_" + settingsFileNameWithoutEnding));
		candidates.add(getDesiredCounterExampleCandidate(inputDir, inputFileNameWithoutEnding));

		for (final File candidate : candidates) {
			if (candidate.canRead()) {
				return CoreUtil.readFile(candidate);
			}
		}
		return null;
	}

	private static File getDesiredCounterExampleCandidate(final String inputDir, final String filename) {
		return new File(String.format("%s%s%s%s", inputDir, IPath.SEPARATOR, filename, ".errorpath"));
	}

	private static String removeFileEnding(final File file) {
		return file.getName().replaceAll("\\..*", "");
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(BacktranslationTestResultDecider.class, mInputFilePath, true, new ArrayList<String>(),
				services);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(final String msg, final Collection<String> customMessages) {
		setResultCategory(msg);
		setResultMessage(msg);
		customMessages.add(msg);
	}

	private boolean tryWritingActualResultToFile(final String actualCounterExample) {
		final String[] actualLines = actualCounterExample.split(CoreUtil.getPlatformLineSeparator());
		try {
			final File input = new File(mInputFilePath);
			final String path = input.getParentFile().getAbsolutePath();
			final String name = removeFileEnding(input) + "_" + removeFileEnding(mRunDefinition.getToolchain()) + "_"
					+ removeFileEnding(mRunDefinition.getSettings());
			final String target = new File(String.format("%s%s%s%s", path, IPath.SEPARATOR, name, ".errorpath-actual"))
					.getAbsolutePath();
			CoreUtil.writeFile(target, actualLines);
			return true;
		} catch (final IOException e) {
			return false;
		}
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private static final class StringCounterexample {

		private final List<StringCounterexampleLine> mLines;

		private StringCounterexample(final String counterexampleAsString) {
			mLines = transformCex(counterexampleAsString);
		}

		private static List<StringCounterexampleLine> transformCex(final String counterexampleAsString) {
			final String platformLineSeparator = CoreUtil.getPlatformLineSeparator();
			final String[] lines = counterexampleAsString.split(platformLineSeparator);
			final List<StringCounterexampleLine> rtr = new ArrayList<>(lines.length);
			for (int i = 0; i < lines.length; ++i) {
				final int j = i + 1;
				final String current = lines[i];
				if (current.trim().startsWith("IVAL")) {
					rtr.add(new StringCounterexampleLine(null, current));
					continue;
				}
				if (j < lines.length) {
					final String next = lines[j];
					if (next.trim().startsWith("VAL")) {
						rtr.add(new StringCounterexampleLine(current, next));
						i = j;
						continue;
					}
				}
				rtr.add(new StringCounterexampleLine(current, null));
			}

			return rtr;
		}

		public Difference getFirstDifference(final StringCounterexample actual) {
			int i = 0;
			for (; i < mLines.size(); ++i) {
				final StringCounterexampleLine desiredLine = mLines.get(i);
				if (i >= actual.mLines.size()) {
					// other has less lines than this
					return new Difference(desiredLine, null);
				}
				final StringCounterexampleLine actualLine = actual.mLines.get(i);
				if (desiredLine.isSimilar(actualLine)) {
					continue;
				}
				return new Difference(desiredLine, actualLine);
			}
			if (i < actual.mLines.size()) {
				// other has more lines than this
				final StringCounterexampleLine actualLine = actual.mLines.get(i);
				return new Difference(null, actualLine);
			}
			return null;
		}
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private static final class StringCounterexampleLine {

		private static final Pattern LINE_REGEX = Pattern.compile("^\\[L(\\d+)\\]\\s+(\\w*)\\s+(.*)$");

		private final String mLine;
		private final String mStmt;
		private final int mLineNumber;
		private final String mLineCategory;
		private final String mValueLine;

		/**
		 * Expects Strings that represent a line of a counterexample and the following value line. Both can be null: the
		 * value line if none is present, and the line if it is the initial value line.
		 * 
		 */
		private StringCounterexampleLine(final String line, final String valueLine) {
			if (line == null) {
				mLine = null;
				mLineCategory = null;
				mStmt = null;
				mLineNumber = -1;
				mValueLine = Objects.requireNonNull(valueLine);
				return;
			}

			final Matcher matcher = LINE_REGEX.matcher(line.trim());
			if (!matcher.find() || matcher.groupCount() != 3) {
				throw new IllegalArgumentException("Line has unexpected format: " + line);
			}
			mLine = Objects.requireNonNull(line);
			mValueLine = valueLine;

			mLineNumber = Integer.parseInt(matcher.group(1));
			String linecat;
			String stmt;
			try {
				linecat = StepInfo.valueOf(matcher.group(2)).name();
				stmt = matcher.group(3);
			} catch (final IllegalArgumentException iae) {
				linecat = null;
				final String g2 = matcher.group(2);
				if (g2.isEmpty()) {
					stmt = matcher.group(3);
				} else {
					stmt = matcher.group(2) + " " + matcher.group(3);
				}
			}
			mLineCategory = linecat;
			mStmt = stmt;
		}

		public boolean isSimilar(final StringCounterexampleLine other) {
			if (mLine == null) {
				if (other.mValueLine == null) {
					return false;
				}
				return isValueLineOk(other.mValueLine, mValueLine);
			}
			if (other.mLineNumber != mLineNumber) {
				return false;
			}
			if (!Objects.equals(mLineCategory, other.mLineCategory)) {
				return false;
			}
			if (!other.mStmt.equals(mStmt)) {
				return false;
			}
			if (other.mValueLine == null || mValueLine == null) {
				if (other.mValueLine == null && mValueLine == null) {
					// both have no value
					return true;
				}
				// one has no value
				return false;
			}
			return isValueLineOk(other.mValueLine, mValueLine);
		}

		/**
		 * @param desiredValue
		 *            A line from the desired error trace
		 * @param actualValue
		 *            The corresponding line from the actual error trace
		 * @return true iff it is a value line and the values do not differ too much (i.e. there is the same number of
		 *         the same variables, but the values do not match)
		 */
		private static boolean isValueLineOk(final String desiredValueLine, final String actualValueLine) {
			final String desiredValue = desiredValueLine.trim();
			final String actualValue = actualValueLine.trim();
			if (desiredValue.startsWith("VAL") && actualValue.startsWith("VAL")
					|| desiredValue.startsWith("IVAL") && actualValue.startsWith("IVAL")) {
				final String[] curDesVals = desiredValue.split(",");
				final String[] curActVals = actualValue.split(",");
				if (curDesVals.length != curActVals.length) {
					return false;
				}

				for (int i = 0; i < curDesVals.length; ++i) {
					final String[] singleDesVal = curDesVals[i].split("=");
					final String[] singleActVal = curActVals[i].split("=");
					if (singleDesVal.length != singleActVal.length) {
						return false;
					}
					// check for the name of the var
					if (!singleDesVal[0].equals(singleActVal[0])) {
						return false;
					}
				}
				return true;
			}
			return false;
		}

		@Override
		public String toString() {
			if (mLine == null) {
				return mValueLine;
			} else if (mValueLine == null) {
				return mLine;
			} else {
				return mLine + " followed by " + mValueLine;
			}
		}
	}

	private static final class Difference {
		private final StringCounterexampleLine mDesired;
		private final StringCounterexampleLine mActual;

		private Difference(final StringCounterexampleLine desired, final StringCounterexampleLine actual) {
			mDesired = desired;
			mActual = actual;
		}

		private List<String> getCustomDifferenceMessage() {
			final List<String> rtr = new ArrayList<>();
			if (mDesired == null) {
				rtr.add("Counterexample should have been shorter, but was identical up to the following line.");
				rtr.add(mActual.toString());
			} else if (mActual == null) {
				rtr.add("Counterexample should have been longer. The next missing line is the following.");
				rtr.add(mDesired.toString());
			} else {
				rtr.add("Counterexamples first differ at the following lines.");
				rtr.add("Desired: " + mDesired.toString());
				rtr.add("Actual: " + mActual.toString());
			}
			return rtr;
		}
	}
}
