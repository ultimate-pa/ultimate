package de.uni_freiburg.informatik.ultimatetest.decider;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;
import de.uni_freiburg.informatik.ultimatetest.util.Util.ExpectedResult;

/**
 * Decide if one of Ultimate's Safety Checkers verified a program correctly.
 * 
 * @author Betim Musa, Matthias Heizmann, dietsch
 * 
 */
public abstract class SafetyCheckTestResultDecider extends TestResultDecider {
	private String mInputFile;
	private ExpectedResult mExpectedResult;

	private Collection<IResult> mResults;

	/**
	 * Result that is returned by the Automizer toolchain.
	 */
	protected enum SafetyCheckerResultType {
		SAFE, UNSAFE, UNKNOWN, SYNTAX_ERROR, TIMEOUT, UNSUPPORTED_SYNTAX, EXCEPTION_OR_ERROR, NO_RESULT;
	}

	protected class SafetyCheckerResult {
		private final IResult m_IResult;
		private final SafetyCheckerResultType m_AutomizerResultType;

		public SafetyCheckerResult(SafetyCheckerResultType automizerResultType, IResult iResult) {
			super();
			m_IResult = iResult;
			m_AutomizerResultType = automizerResultType;
		}

		public IResult getIResult() {
			return m_IResult;
		}

		public SafetyCheckerResultType getAutomizerResultType() {
			return m_AutomizerResultType;
		}

	}

	public SafetyCheckTestResultDecider(File inputFile) {
		super();
		mInputFile = inputFile.getAbsolutePath();
		generateExpectedResult(inputFile);
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services) {
		Logger log = Logger.getLogger(SafetyCheckTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		final TestResult testoutcome;
		mResults = new ArrayList<IResult>();
		for (Entry<String, List<IResult>> entry : services.getResultService().getResults().entrySet()) {
			mResults.addAll(entry.getValue());
		}

		ExpectedResult expected = getExpectedResult();
		if (expected != null) {
			customMessages.add("Expected Result: " + expected);
		}

		if (expected == ExpectedResult.NOANNOTATION) {
			customMessages.add("Couldn't understand the specification of the file \"" + mInputFile + "\".\n"
					+ "Use //#Safe or //#Unsafe to indicate that the program is safe resp. unsafe. Use "
					+ "//#NoSpec if there is still no decision about the specification.");
		}
		SafetyCheckerResult scResult = getSafetyCheckerResult(mResults);
		if (scResult == null) {
			testoutcome = TestResult.FAIL;
		} else {
			switch (scResult.getAutomizerResultType()) {
			case EXCEPTION_OR_ERROR:
				testoutcome = TestResult.FAIL;
				break;
			case SAFE:
				if (expected == ExpectedResult.SAFE) {
					testoutcome = TestResult.SUCCESS;
				} else if (expected == ExpectedResult.NOANNOTATION) {
					testoutcome = TestResult.UNKNOWN;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case UNSAFE:
				if (expected == ExpectedResult.UNSAFE) {
					testoutcome = TestResult.SUCCESS;
				} else if (expected == ExpectedResult.NOANNOTATION) {
					testoutcome = TestResult.UNKNOWN;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case UNKNOWN:
				// syntax error should always have been found
				if (expected == ExpectedResult.SYNTAXERROR) {
					testoutcome = TestResult.FAIL;
				} else {
					testoutcome = TestResult.UNKNOWN;
				}
				break;
			case SYNTAX_ERROR:
				if (expected == ExpectedResult.SYNTAXERROR) {
					testoutcome = TestResult.SUCCESS;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case TIMEOUT:
				// syntax error should always have been found
				if (expected == ExpectedResult.SYNTAXERROR) {
					testoutcome = TestResult.FAIL;
				} else {
					testoutcome = TestResult.UNKNOWN;
				}
				break;
			case UNSUPPORTED_SYNTAX:
				testoutcome = TestResult.FAIL;
				break;
			case NO_RESULT:
				testoutcome = TestResult.FAIL;
				break;
			default:
				throw new AssertionError("unknown case");
			}
		}

		generateResultMessageAndCategory(scResult);
		Util.logResults(log, mInputFile, !getJUnitTestResult(testoutcome), customMessages, services.getResultService());
		return testoutcome;
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services, Throwable e) {
		generateResultMessageAndCategory(new SafetyCheckerResult(SafetyCheckerResultType.EXCEPTION_OR_ERROR,
				new ExceptionOrErrorResult("Ultimate", e)));
		Logger log = Logger.getLogger(SafetyCheckTestResultDecider.class);
		Util.logResults(log, mInputFile, true, new LinkedList<String>(), services.getResultService());
		return TestResult.FAIL;
	}

	/**
	 * Generate the expected result for the current test (i.e. call
	 * {@link #setExpectedResult(ExpectedResult)}.
	 * 
	 * Is called in the constructor.
	 * 
	 * This method should be overwritten by clients providing ExpectedResults
	 * for different kinds of file annotations.
	 * 
	 * @param inputFile
	 *            The current input file.
	 * @return
	 */
	protected void generateExpectedResult(File inputFile) {
		if (getExpectedResult() == null) {
			setExpectedResult(Util.getExpectedResult(inputFile));
		}
	}

	protected ExpectedResult getExpectedResult() {
		return mExpectedResult;
	}

	protected void setExpectedResult(ExpectedResult expectedResult) {
		mExpectedResult = expectedResult;
	}

	/**
	 * This method is called to create a
	 * {@link ITestResultDecider#getResultMessage() result message} and
	 * {@link ITestResultDecider#getResultCategory() result category} from a
	 * {@link SafetyCheckerResult}, which already decided (based on expected
	 * result and actual result) what the overall result of the current test
	 * case should be.
	 * 
	 * If your {@link SafetyCheckTestResultDecider} is not used to support
	 * summaries, you should overwrite this method to prevent the generation of
	 * those Strings.
	 * 
	 * @param safetyCheckerResult
	 *            The {@link SafetyCheckerResult} describing the actual result
	 *            of this test.
	 * 
	 */
	protected void generateResultMessageAndCategory(SafetyCheckerResult safetyCheckerResult) {
		if (safetyCheckerResult == null) {
			// TODO: It may happen, you have to choose which category this gets
			// (happens e.g. when the toolchain file is corrupt)
			return;
		}
		if (safetyCheckerResult.getAutomizerResultType() == SafetyCheckerResultType.EXCEPTION_OR_ERROR) {
			setResultMessage("Error: " + safetyCheckerResult.getIResult().getLongDescription());
		} else if (getExpectedResult() == ExpectedResult.NOANNOTATION) {
			setResultMessage("File was neither annotated nor does the filename contain a specification."
					+ "\tModel checker says: " + safetyCheckerResult.getAutomizerResultType().toString());
		} else {
			setResultMessage("Annotation says: " + getExpectedResult() + "\tModel checker says: "
					+ safetyCheckerResult.getAutomizerResultType().toString());
		}

		IResult iResult = safetyCheckerResult.getIResult();
		if (iResult != null) {
			setResultMessage(getResultMessage() + "\t ShortDescription: " + iResult.getShortDescription());
			setResultMessage(getResultMessage() + "\t LongDescription: " + iResult.getLongDescription());
		}

		setResultCategory(safetyCheckerResult.getAutomizerResultType().toString());
	}

	private SafetyCheckerResult getSafetyCheckerResult(Collection<IResult> results) {
		final SafetyCheckerResult returnValue;
		Map<SafetyCheckerResultType, SafetyCheckerResult> resultSet = new HashMap<SafetyCheckerResultType, SafetyCheckerResult>();
		for (IResult result : results) {
			SafetyCheckerResult extracted = extractResult(result);
			if (extracted != null) {
				resultSet.put(extracted.getAutomizerResultType(), extracted);
			}
		}
		if (resultSet.containsKey(SafetyCheckerResultType.EXCEPTION_OR_ERROR)) {
			returnValue = resultSet.get(SafetyCheckerResultType.EXCEPTION_OR_ERROR);
		} else if (resultSet.containsKey(SafetyCheckerResultType.SYNTAX_ERROR)) {
			if (resultSet.size() > 1) {
				throw new AssertionError("no other result allowed");
			} else {
				returnValue = resultSet.get(SafetyCheckerResultType.SYNTAX_ERROR);
			}
		} else if (resultSet.containsKey(SafetyCheckerResultType.UNSUPPORTED_SYNTAX)) {
			if (resultSet.size() > 1) {
				throw new AssertionError("no other result allowed");
			} else {
				returnValue = resultSet.get(SafetyCheckerResultType.UNSUPPORTED_SYNTAX);
			}
		} else if (resultSet.containsKey(SafetyCheckerResultType.SAFE)) {
			returnValue = resultSet.get(SafetyCheckerResultType.SAFE);
		} else if (resultSet.containsKey(SafetyCheckerResultType.UNSAFE)) {
			returnValue = resultSet.get(SafetyCheckerResultType.UNSAFE);
		} else if (resultSet.containsKey(SafetyCheckerResultType.UNKNOWN)) {
			returnValue = resultSet.get(SafetyCheckerResultType.UNKNOWN);
		} else if (resultSet.containsKey(SafetyCheckerResultType.TIMEOUT)) {
			returnValue = resultSet.get(SafetyCheckerResultType.TIMEOUT);
		} else {
			returnValue = resultSet.get(SafetyCheckerResultType.NO_RESULT);
		}
		assert returnValue != null : "no result!";
		return returnValue;
	}

	private SafetyCheckerResult extractResult(IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.SAFE, result);
		} else if (result instanceof CounterExampleResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.UNSAFE, null);
		} else if (result instanceof UnprovableResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.UNKNOWN, null);
		} else if (result instanceof TypeErrorResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.SYNTAX_ERROR, result);
		} else if (result instanceof SyntaxErrorResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.SYNTAX_ERROR, result);
		} else if (result instanceof ITimeoutResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.TIMEOUT, null);
		} else if (result instanceof UnsupportedSyntaxResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.UNSUPPORTED_SYNTAX, result);
		} else if (result instanceof ExceptionOrErrorResult) {
			return new SafetyCheckerResult(SafetyCheckerResultType.EXCEPTION_OR_ERROR, result);
		} else {
			return null;
		}
	}

}
