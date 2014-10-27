package de.uni_freiburg.informatik.ultimatetest.decider;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Path;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BacktranslationTestResultDecider extends TestResultDecider {

	private final String mInputFile;
	private final String mFileEnding;

	/**
	 * 
	 * @param inputFile
	 * @param fileending
	 *            use .c or .bpl or something like that. The . is important
	 * 
	 */
	public BacktranslationTestResultDecider(String inputFile, String fileending) {
		mInputFile = inputFile;
		mFileEnding = fileending;
	}

	@Override
	public TestResult getTestResult(IResultService resultService) {

		setResultCategory("");
		setResultMessage("");

		Logger log = Logger.getLogger(BacktranslationTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		customMessages.add("Expecting results to not contain GenericResult \"Unhandled Backtranslation\" "
				+ "or ExceptionOrErrorResult, "
				+ "and that there is a counter example result, and that the contained error trace "
				+ "matches the given one.");
		boolean fail = false;
		ArrayList<CounterExampleResult<?, ?, ?>> cex = new ArrayList<>();
		Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (Entry<String, List<IResult>> x : resultSet) {
			for (IResult result : x.getValue()) {
				if (result instanceof ExceptionOrErrorResult) {
					setCategoryAndMessageAndCustomMessage(result.getShortDescription(), customMessages);
					fail = true;
					break;
				} else if (result instanceof GenericResult) {
					GenericResult genRes = (GenericResult) result;
					if (genRes.getShortDescription().equals("Unfinished Backtranslation")) {
						setResultCategory(result.getShortDescription());
						setResultMessage(result.getLongDescription());
						customMessages.add(result.getShortDescription() + ": " + result.getLongDescription());
						fail = true;
					}
				} else if (result instanceof CounterExampleResult<?, ?, ?>) {
					cex.add((CounterExampleResult<?, ?, ?>) result);
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

		if (!fail) {
			// so far so good, now we compare the error path with the expected
			// error path

			File inputFile = new File(mInputFile);
			String inputFileNameWithoutEnding = inputFile.getName().replaceAll("\\" + mFileEnding, "");
			File desiredCounterExampleFile = new File(String.format("%s%s%s%s", inputFile.getParentFile()
					.getAbsolutePath(), Path.SEPARATOR, inputFileNameWithoutEnding, ".errorpath"));
			String actualCounterExample = cex.get(0).getProgramExecutionAsString();
			if (desiredCounterExampleFile.canRead()) {

				try {
					String desiredCounterExample = Util.readFile(desiredCounterExampleFile);

					// compare linewise
					String platformLineSeparator = Util.getPlatformLineSeparator();
					String[] desiredLines = desiredCounterExample.split(platformLineSeparator);
					String[] actualLines = actualCounterExample.split(platformLineSeparator);

					if (desiredLines.length != actualLines.length) {
						fail = true;
					} else {
						for (int i = 0; i < desiredLines.length; ++i) {
							String curDes = desiredLines[i].trim();
							String curAct = actualLines[i].trim();
							if (!(curDes.equals(curAct))) {
								fail = true;
								break;
							}
						}
					}

					if (fail) {
						tryWritingActualResultToFile(desiredCounterExampleFile, actualCounterExample);
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

				} catch (IOException e) {
					setResultCategory(e.getMessage());
					setResultMessage(e.toString());
					e.printStackTrace();
					fail = true;
				}
			} else {
				setResultCategory("No .errorpath file for comparison");
				String errorMsg = String.format("There is no .errorpath file for %s!", mInputFile);
				tryWritingActualResultToFile(desiredCounterExampleFile, actualCounterExample);
				setResultMessage(errorMsg);
				customMessages.add(errorMsg);
				fail = true;
			}

		}
		Util.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(IResultService resultService, Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		Util.logResults(Logger.getLogger(BacktranslationTestResultDecider.class), mInputFile, true,
				new ArrayList<String>(), resultService);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(String msg, Collection<String> customMessages) {
		setResultCategory(msg);
		setResultMessage(msg);
		customMessages.add(msg);
	}

	private boolean tryWritingActualResultToFile(File desiredCounterExampleFile, String actualCounterExample) {
		String[] actualLines = actualCounterExample.split(Util.getPlatformLineSeparator());
		try {
			Util.writeFile(desiredCounterExampleFile.getAbsolutePath() + "-actual", actualLines);
			return true;
		} catch (IOException e) {
			return false;
		}
	}

}