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

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.WitnessResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BacktranslationTestResultDecider extends TestResultDecider {

	private final String mInputFile;
	private final String mFileEnding;
	private final String mSettingsFile;

	/**
	 * 
	 * @param inputFile
	 * @param settingsFile
	 * @param fileending
	 *            use .c or .bpl or something like that. The . is important
	 * 
	 * 
	 */
	public BacktranslationTestResultDecider(String inputFile, String settingsFile, String fileending) {
		mInputFile = inputFile;
		mSettingsFile = settingsFile;
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
		ArrayList<WitnessResult<?, ?, ?>> witnesses = new ArrayList<>();
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
				} else if (result instanceof WitnessResult<?, ?, ?>) {
					witnesses.add((WitnessResult<?, ?, ?>) result);
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

		if (mFileEnding.equals(".c")
				&& new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
						.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_VERIFY)) {
			// we expect witness verification for .c files to succeed

			if (cex.size() != witnesses.size()) {
				setResultCategory("Not all counter examples have witnesses");
				String errorMsg = "There were " + cex.size() + " counter examples, but " + witnesses.size()
						+ " witnesses";
				setResultMessage(errorMsg);
				customMessages.add(errorMsg);
				fail = true;

			} else {
				for (WitnessResult<?, ?, ?> witness : witnesses) {
					if (witness.isEmpty()) {
						setResultCategory("Empty Witness");
						String errorMsg = "The witness is empty: " + witness.getShortDescription();
						setResultMessage(errorMsg);
						customMessages.add(errorMsg);
						fail = true;
						break;
					} else if (!witness.isVerified()) {
						setResultCategory("Witness failed to verify");
						String errorMsg = "The witness failed to verify: " + witness.getLongDescription();
						setResultMessage(errorMsg);
						customMessages.add(errorMsg);
						fail = true;
						break;
					}
				}
			}
		}

		if (!fail) {
			// so far so good, now we compare the error path with the expected
			// error path

			File inputFile = new File(mInputFile);
			File settingsFile = new File(mSettingsFile);
			String desiredCounterExample = null;
			try {
				desiredCounterExample = getDesiredCounterExample(inputFile, settingsFile);
			} catch (IOException e) {
				setResultCategory(e.getMessage());
				setResultMessage(e.toString());
				e.printStackTrace();
				Util.logResults(log, mInputFile, true, customMessages, resultService);
				return TestResult.FAIL;
			}

			String actualCounterExample = cex.get(0).getProgramExecutionAsString();
			if (desiredCounterExample == null) {
				setResultCategory("No .errorpath file for comparison");
				String errorMsg = String.format("There is no .errorpath file for %s!", mInputFile);
				tryWritingActualResultToFile(actualCounterExample);
				setResultMessage(errorMsg);
				customMessages.add(errorMsg);
				fail = true;
			} else {

				// compare linewise
				String platformLineSeparator = de.uni_freiburg.informatik.ultimate.core.util.CoreUtil
						.getPlatformLineSeparator();
				String[] desiredLines = desiredCounterExample.split(platformLineSeparator);
				String[] actualLines = actualCounterExample.split(platformLineSeparator);

				if (desiredLines.length != actualLines.length) {
					fail = true;
				} else {
					for (int i = 0; i < desiredLines.length; ++i) {
						String curDes = desiredLines[i].trim();
						String curAct = actualLines[i].trim();
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
		Util.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	private String getDesiredCounterExample(File inputFile, File settingsFile) throws IOException {
		String inputFileNameWithoutEnding = removeFileEnding(inputFile);
		String settingsFileNameWithoutEnding = removeFileEnding(settingsFile);

		// order some candidates which we would like, we take the first that
		// matches
		ArrayList<File> candidates = new ArrayList<>();
		candidates.add(new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(), Path.SEPARATOR,
				inputFileNameWithoutEnding + "_" + settingsFileNameWithoutEnding, ".errorpath")));
		candidates.add(new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(), Path.SEPARATOR,
				inputFileNameWithoutEnding, ".errorpath")));

		for (File candidate : candidates) {
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
	 *            The corresponding line from the actual error trace, already
	 *            trimmed
	 * @return true iff it is a value line and the values do not differ too much
	 *         (i.e. there is the same number of the same variables, but the
	 *         values do not match)
	 */
	private boolean isValueLineOk(String curDes, String curAct) {

		if ((curDes.startsWith("VAL") && curAct.startsWith("VAL"))
				|| (curDes.startsWith("IVAL") && curAct.startsWith("IVAL")))

		{
			String[] curDesVals = curDes.split(",");
			String[] curActVals = curAct.split(",");
			if (curDesVals.length != curActVals.length) {
				return false;
			}

			for (int i = 0; i < curDesVals.length; ++i) {
				String[] singleDesVal = curDesVals[i].split("=");
				String[] singleActVal = curActVals[i].split("=");
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