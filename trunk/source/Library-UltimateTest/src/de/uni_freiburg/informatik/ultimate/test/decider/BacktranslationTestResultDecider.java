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
import java.util.Optional;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.Path;

import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.WitnessResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.WitnessResult.WitnessVerificationStatus;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BacktranslationTestResultDecider extends TestResultDecider {

	private final String mInputFile;
	private final String mSettingsFile;

	/**
	 * 
	 * @param inputFile
	 * @param settingsFile
	 * @param fileending
	 *            use .c or .bpl or something like that. The . is important
	 * 
	 */
	public BacktranslationTestResultDecider(final File inputFile, final String settingsFile, final String fileending) {
		mInputFile = inputFile.getAbsolutePath();
		mSettingsFile = settingsFile;
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {

		setResultCategory("");
		setResultMessage("");

		final ILogger log = services.getLoggingService().getLogger(BacktranslationTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<String>();
		customMessages.add("Expecting results to not contain GenericResult \"Unhandled Backtranslation\" "
				+ ", ExceptionOrErrorResult or TypeErrorResult, "
				+ "and that there is a counter example result, and that the contained error trace "
				+ "matches the given one.");

		final List<CounterExampleResult<?, ?, ?>> cex = new ArrayList<>();
		final List<WitnessResult> witnesses = new ArrayList<>();
		final IResultService resultService = services.getResultService();

		final List<IResult> results = resultService.getResults().entrySet().stream().flatMap(a -> a.getValue().stream())
				.collect(Collectors.toList());
		for (final IResult result : results) {
			if (result instanceof ExceptionOrErrorResult || result instanceof TypeErrorResult<?>
					|| result instanceof SyntaxErrorResult) {
				setCategoryAndMessageAndCustomMessage(result.getShortDescription(), customMessages);
				TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
				return TestResult.FAIL;
			} else if (result instanceof GenericResult) {
				final GenericResult genRes = (GenericResult) result;
				if (genRes.getShortDescription().equals("Unfinished Backtranslation")) {
					setResultCategory(result.getShortDescription());
					setResultMessage(result.getLongDescription());
					customMessages.add(result.getShortDescription() + ": " + result.getLongDescription());
					TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
					return TestResult.FAIL;
				}
			} else if (result instanceof CounterExampleResult<?, ?, ?>) {
				cex.add((CounterExampleResult<?, ?, ?>) result);
			} else if (result instanceof WitnessResult) {
				witnesses.add((WitnessResult) result);
			}
		}

		if (cex.size() == 0) {
			setCategoryAndMessageAndCustomMessage("No counter example found", customMessages);
			TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
			return TestResult.FAIL;
		}
		if (cex.size() > 1) {
			setResultCategory("More than one counter example found");
			final String errorMsg = "There were " + cex.size() + " counter examples, but we expected only one";
			setResultMessage(errorMsg);
			customMessages.add(errorMsg);
			TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
			return TestResult.FAIL;
		}

		final List<WitnessResult> witnessesWithCex = new ArrayList<>();
		for (final IResult result : cex) {
			final Optional<WitnessResult> witness =
					witnesses.stream().filter(a -> a.getAffectedResult() == result).findAny();
			if (witness.isPresent()) {
				witnessesWithCex.add(witness.get());
			}
		}

		if (!witnessesWithCex.isEmpty()) {
			// we expect witness verification for .c files to succeed
			for (final WitnessResult witness : witnessesWithCex) {
				if (witness.isEmpty()) {
					setResultCategory("Empty Witness");
					final String errorMsg = "The witness is empty: " + witness.getShortDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
					return TestResult.FAIL;
				} else if (witness.getExpectedVerificationStatus() == WitnessVerificationStatus.VERIFIED
						&& witness.getVerificationStatus() != WitnessVerificationStatus.VERIFIED) {
					setResultCategory("Witness failed to verify");
					final String errorMsg = "The witness failed to verify: " + witness.getLongDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
					return TestResult.FAIL;
				}
			}
		}

		// so far so good, now we compare the error path with the expected
		// error path
		boolean fail = false;
		final File inputFile = new File(mInputFile);
		final File settingsFile = new File(mSettingsFile);
		String desiredCounterExample = null;
		try {
			desiredCounterExample = getDesiredCounterExample(inputFile, settingsFile);
		} catch (final IOException e) {
			setResultCategory(e.getMessage());
			setResultMessage(e.toString());
			e.printStackTrace();
			TestUtil.logResults(log, mInputFile, true, customMessages, resultService);
			return TestResult.FAIL;
		}

		final String actualCounterExample = cex.get(0).getProgramExecutionAsString();
		if (desiredCounterExample == null) {
			setResultCategory("No .errorpath file for comparison");
			final String errorMsg = String.format("There is no .errorpath file for %s!", mInputFile);
			tryWritingActualResultToFile(actualCounterExample);
			setResultMessage(errorMsg);
			customMessages.add(errorMsg);
			fail = true;
		} else {

			// compare linewise
			final String platformLineSeparator = CoreUtil.getPlatformLineSeparator();
			final String[] desiredLines = desiredCounterExample.split(platformLineSeparator);
			final String[] actualLines = actualCounterExample.split(platformLineSeparator);

			if (desiredLines.length != actualLines.length) {
				fail = true;
			} else {
				for (int i = 0; i < desiredLines.length; ++i) {
					final String curDes = desiredLines[i].trim();
					final String curAct = actualLines[i].trim();
					if (!(curDes.equals(curAct))) {
						// ok it does not match, but we may make an
						// exception for value lines
						if (!isValueLineOk(curDes, curAct)) {
							// it is either not a value line or the
							// value lines differ too much
							fail = true;
							break;
						}
					}
				}
			}

			if (fail) {
				tryWritingActualResultToFile(actualCounterExample);
				setCategoryAndMessageAndCustomMessage("Desired error trace does not match actual error trace.",
						customMessages);
				customMessages.add("Lengths: Desired=" + desiredCounterExample.length() + " Actual="
						+ actualCounterExample.length());
				customMessages.add("Desired error trace:");
				int i = 0;
				for (final String s : desiredCounterExample.split(platformLineSeparator)) {
					customMessages.add("[L" + i + "] " + s);
					++i;
				}
				i = 0;
				customMessages.add("Actual error trace:");
				for (final String s : actualCounterExample.split(platformLineSeparator)) {
					customMessages.add("[L" + i + "] " + s);
					++i;
				}
			} else {
				setResultCategory("Success");
			}
		}
		TestUtil.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	private String getDesiredCounterExample(final File inputFile, final File settingsFile) throws IOException {
		final String inputFileNameWithoutEnding = removeFileEnding(inputFile);
		final String settingsFileNameWithoutEnding = removeFileEnding(settingsFile);

		// order some candidates which we would like, we take the first that
		// matches
		final List<File> candidates = new ArrayList<>();
		candidates.add(new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(), Path.SEPARATOR,
				inputFileNameWithoutEnding + "_" + settingsFileNameWithoutEnding, ".errorpath")));
		candidates.add(new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(), Path.SEPARATOR,
				inputFileNameWithoutEnding, ".errorpath")));

		for (final File candidate : candidates) {
			if (candidate.canRead()) {
				return CoreUtil.readFile(candidate);
			}
		}
		return null;
	}

	private String removeFileEnding(final File file) {
		return file.getName().replaceAll("\\..*", "");
	}

	/**
	 * 
	 * @param curDes
	 *            A line from the desired error trace, already trimmed
	 * @param curAct
	 *            The corresponding line from the actual error trace, already trimmed
	 * @return true iff it is a value line and the values do not differ too much (i.e. there is the same number of the
	 *         same variables, but the values do not match)
	 */
	private boolean isValueLineOk(final String curDes, final String curAct) {

		if ((curDes.startsWith("VAL") && curAct.startsWith("VAL"))
				|| (curDes.startsWith("IVAL") && curAct.startsWith("IVAL")))

		{
			final String[] curDesVals = curDes.split(",");
			final String[] curActVals = curAct.split(",");
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
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(BacktranslationTestResultDecider.class, mInputFile, true, new ArrayList<String>(),
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
			final File input = new File(mInputFile);
			final String path = input.getParentFile().getAbsolutePath();
			final String name = removeFileEnding(input) + "_" + (removeFileEnding(new File(mSettingsFile)));
			final String target = new File(String.format("%s%s%s%s", path, Path.SEPARATOR, name, ".errorpath-actual"))
					.getAbsolutePath();
			CoreUtil.writeFile(target, actualLines);
			return true;
		} catch (final IOException e) {
			return false;
		}
	}
}
