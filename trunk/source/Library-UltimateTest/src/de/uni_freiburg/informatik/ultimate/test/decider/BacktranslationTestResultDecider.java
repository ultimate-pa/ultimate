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
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import org.eclipse.core.runtime.Path;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.WitnessResult;
import de.uni_freiburg.informatik.ultimate.result.WitnessResult.WitnessVerificationStatus;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
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
				+ "or ExceptionOrErrorResult, "
				+ "and that there is a counter example result, and that the contained error trace "
				+ "matches the given one.");
		boolean fail = false;
		final List<CounterExampleResult<?, ?, ?>> cex = new ArrayList<>();
		final List<WitnessResult> witnesses = new ArrayList<>();
		final IResultService resultService = services.getResultService();
		final Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (final Entry<String, List<IResult>> x : resultSet) {
			for (final IResult result : x.getValue()) {
				if (result instanceof ExceptionOrErrorResult) {
					setCategoryAndMessageAndCustomMessage(result.getShortDescription(), customMessages);
					fail = true;
					break;
				} else if (result instanceof GenericResult) {
					final GenericResult genRes = (GenericResult) result;
					if (genRes.getShortDescription().equals("Unfinished Backtranslation")) {
						setResultCategory(result.getShortDescription());
						setResultMessage(result.getLongDescription());
						customMessages.add(result.getShortDescription() + ": " + result.getLongDescription());
						fail = true;
					}
				} else if (result instanceof CounterExampleResult<?, ?, ?>) {
					cex.add((CounterExampleResult<?, ?, ?>) result);
				} else if (result instanceof WitnessResult) {
					witnesses.add((WitnessResult) result);
				}
			}
		}

		if (cex.size() == 0) {
			setCategoryAndMessageAndCustomMessage("No counter example found", customMessages);
			fail = true;
		}
		if (cex.size() > 1) {
			setResultCategory("More than one counter example found");
			String errorMsg = "There were " + cex.size() + " counter examples, but we expected only one";
			setResultMessage(errorMsg);
			customMessages.add(errorMsg);
			fail = true;
		}

		final List<WitnessResult> witnessesWithCex = new ArrayList<>();
		for (final IResult result : cex) {
			final Optional<WitnessResult> witness = witnesses.stream().filter(a -> a.getAffectedResult() == result)
					.findAny();
			if (witness.isPresent()) {
				witnessesWithCex.add(witness.get());
			}
		}

		if (!witnessesWithCex.isEmpty()) {
			// we expect witness verification for .c files to succeed
			for (final WitnessResult witness : witnessesWithCex) {
				if (witness.isEmpty()) {
					setResultCategory("Empty Witness");
					String errorMsg = "The witness is empty: " + witness.getShortDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					fail = true;
					break;
				} else if (witness.getExpectedVerificationStatus() == WitnessVerificationStatus.VERIFIED
						&& witness.getVerificationStatus() != WitnessVerificationStatus.VERIFIED) {
					setResultCategory("Witness failed to verify");
					String errorMsg = "The witness failed to verify: " + witness.getLongDescription();
					setResultMessage(errorMsg);
					customMessages.add(errorMsg);
					fail = true;
					break;
				}
			}
		}

		if (!fail) {
			// so far so good, now we compare the error path with the expected
			// error path

			final File inputFile = new File(mInputFile);
			final File settingsFile = new File(mSettingsFile);
			String desiredCounterExample = null;
			try {
				desiredCounterExample = getDesiredCounterExample(inputFile, settingsFile);
			} catch (IOException e) {
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
				final String platformLineSeparator = de.uni_freiburg.informatik.ultimate.util.CoreUtil
						.getPlatformLineSeparator();
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
					for (String s : desiredCounterExample.split(platformLineSeparator)) {
						customMessages.add("[L" + i + "] " + s);
						++i;
					}
					i = 0;
					customMessages.add("Actual error trace:");
					for (String s : actualCounterExample.split(platformLineSeparator)) {
						customMessages.add("[L" + i + "] " + s);
						++i;
					}
				} else {
					setResultCategory("Success");
				}
			}
		}
		TestUtil.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	private String getDesiredCounterExample(File inputFile, File settingsFile) throws IOException {
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

	private String removeFileEnding(File file) {
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
	private boolean isValueLineOk(String curDes, String curAct) {

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
	public TestResult getTestResult(final IUltimateServiceProvider services, Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(BacktranslationTestResultDecider.class, mInputFile, true, new ArrayList<String>(),
				services);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(String msg, Collection<String> customMessages) {
		setResultCategory(msg);
		setResultMessage(msg);
		customMessages.add(msg);
	}

	private boolean tryWritingActualResultToFile(String actualCounterExample) {
		String[] actualLines = actualCounterExample.split(CoreUtil.getPlatformLineSeparator());
		try {
			File input = new File(mInputFile);
			String path = input.getParentFile().getAbsolutePath();
			String name = removeFileEnding(input) + "_" + (removeFileEnding(new File(mSettingsFile)));
			String target = new File(String.format("%s%s%s%s", path, Path.SEPARATOR, name, ".errorpath-actual"))
					.getAbsolutePath();
			CoreUtil.writeFile(target, actualLines);
			return true;
		} catch (IOException e) {
			return false;
		}
	}
}
