/*
 * Copyright (C) 2015 Christopher Dillo
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.test.decider;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 * Took stuff from the old SafetyCheckTestResultDecider_OldVersion 'cause there was so much I had to adjust for my own
 * needs and I don't want to dig into the new one to see if it suits me better
 * 
 * @author Christopher Dillo
 */
public class AbstractInterpretationTestResultDecider extends TestResultDecider {

	public enum ExpectedResultType {
		SAFE, UNSAFE, SYNTAXERROR, NOANNOTATION
	}

	public enum ActualResultType {
		SAFE, UNSAFE, UNKNOWN, SYNTAX_ERROR, TIMEOUT, UNSUPPORTED_SYNTAX, EXCEPTION_OR_ERROR, NO_RESULT;
	}

	protected class ActualResult {
		private final IResult mIResult;
		private final ActualResultType mactualResultType;

		public ActualResult(final ActualResultType automizerResultType, final IResult iResult) {
			mIResult = iResult;
			mactualResultType = automizerResultType;
		}

		public IResult getIResult() {
			return mIResult;
		}

		public ActualResultType getResultType() {
			return mactualResultType;
		}
	}

	private final String mInputFile;

	private final String mtoolIdentifier;

	private ExpectedResultType mexpectedResult;

	private Collection<IResult> mResults;

	/** Peak memory in MiB **/
	private String mResultMemory = "";
	/** Runtime in ms **/
	private String mResultTime = "";

	/**
	 * @param inputFile
	 *            Well duh ;-)
	 * @param toolIdentifier
	 *            Used to identify which tool the result belongs to.
	 */
	public AbstractInterpretationTestResultDecider(final File inputFile, final String toolIdentifier) {
		super();
		mInputFile = inputFile.getAbsolutePath();
		mtoolIdentifier = toolIdentifier;
		generateExpectedResult(inputFile);
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {
		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(AbstractInterpretationTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<>();
		final TestResult testoutcome;
		mResults = new ArrayList<>();

		for (final Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			mResults.addAll(entry.getValue());
		}

		// get benchmark result stuff
		for (final IResult r : mResults) {
			if (r instanceof BenchmarkResult) {
				final BenchmarkResult<?> br = (BenchmarkResult<?>) r;
				final ICsvProviderProvider<?> ic = br.getBenchmark();

				if (ic instanceof Benchmark) {
					final Benchmark benchmark = (Benchmark) ic;

					long memory = 0; // in bytes
					double time = 0; // in milliseconds

					for (final String title : benchmark.getTitles()) {
						final long watchMem =
								benchmark.getStartHeapSize(title) + benchmark.getPeakMemoryConsumed(title);
						if (watchMem > memory) {
							memory = watchMem;
						}
						time += benchmark.getElapsedTime(title, TimeUnit.MILLISECONDS);
					}

					mResultMemory = String.format("%d", memory / 1024 / 1024); // -> MiB
					mResultTime = String.format("%.0f", time);
				}
			}
		}

		final ExpectedResultType expected = getExpectedResult();
		if (expected != null) {
			customMessages.add("Expected Result: " + expected);
		}

		if (expected == ExpectedResultType.NOANNOTATION) {
			customMessages.add("Couldn't understand the specification of the file \"" + mInputFile + "\".");
		}
		final ActualResult scResult = getActualResult(mResults);
		if (scResult == null) {
			testoutcome = TestResult.FAIL;
		} else {
			switch (scResult.getResultType()) {
			case EXCEPTION_OR_ERROR:
				testoutcome = TestResult.FAIL;
				break;
			case SAFE:
				if (expected == ExpectedResultType.SAFE) {
					testoutcome = TestResult.SUCCESS;
				} else if (expected == ExpectedResultType.NOANNOTATION) {
					testoutcome = TestResult.UNKNOWN;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case UNSAFE:
				if (expected == ExpectedResultType.UNSAFE) {
					testoutcome = TestResult.SUCCESS;
				} else if (expected == ExpectedResultType.NOANNOTATION) {
					testoutcome = TestResult.UNKNOWN;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case UNKNOWN:
				// syntax error should always have been found
				if (expected == ExpectedResultType.SYNTAXERROR) {
					testoutcome = TestResult.FAIL;
				} else if (expected == ExpectedResultType.UNSAFE) {
					testoutcome = TestResult.SUCCESS;
				} else {
					testoutcome = TestResult.UNKNOWN;
				}
				break;
			case SYNTAX_ERROR:
				if (expected == ExpectedResultType.SYNTAXERROR) {
					testoutcome = TestResult.SUCCESS;
				} else {
					testoutcome = TestResult.FAIL;
				}
				break;
			case TIMEOUT:
				// syntax error should always have been found
				if (expected == ExpectedResultType.SYNTAXERROR) {
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
		TestUtil.logResults(log, mInputFile, !getJUnitSuccess(testoutcome), customMessages, resultService);
		return testoutcome;
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider service, final Throwable e) {
		generateResultMessageAndCategory(
				new ActualResult(ActualResultType.EXCEPTION_OR_ERROR, new ExceptionOrErrorResult("Ultimate", e)));
		TestUtil.logResults(AbstractInterpretationTestResultDecider.class, mInputFile, true, new LinkedList<String>(),
				service);
		return TestResult.FAIL;
	}

	protected void generateExpectedResult(final File inputFile) {
		if (getExpectedResult() == null) {
			setExpectedResult(getExpectedResult(inputFile));
		}
	}

	public static ExpectedResultType getExpectedResult(final File inputFile) {
		final String line = TestUtil.extractFirstLine(inputFile);
		if (line != null) {
			if (line.contains("#Safe") || line.contains("iSafe")) {
				return ExpectedResultType.SAFE;
			} else if (line.contains("#Unsafe") || line.contains("iUnsafe")) {
				return ExpectedResultType.UNSAFE;
			} else if (line.contains("#SyntaxError")) {
				return ExpectedResultType.SYNTAXERROR;
			}
		}
		final String lowercaseFilename = inputFile.getName().toLowerCase();
		if (lowercaseFilename.contains("-safe") || lowercaseFilename.contains("_safe")
				|| lowercaseFilename.contains("true-unreach-call")) {
			return ExpectedResultType.SAFE;
		} else if (lowercaseFilename.contains("-unsafe") || lowercaseFilename.contains("_unsafe")
				|| lowercaseFilename.contains("false-unreach-call")) {
			return ExpectedResultType.UNSAFE;
		}
		return ExpectedResultType.NOANNOTATION;
	}

	protected ExpectedResultType getExpectedResult() {
		return mexpectedResult;
	}

	protected void setExpectedResult(final ExpectedResultType expectedResult) {
		mexpectedResult = expectedResult;
	}

	/**
	 * Message: Symbol for the LaTeX table denoting the expected result.
	 */
	protected void generateResultMessageAndCategory(final ActualResult safetyCheckerResult) {
		if (safetyCheckerResult == null) {
			setResultMessage("NULL ## NULL ## NULL ## NULL ## NULL OH NO");
			setResultCategory("NULL ## NULL ## NULL OH NO");
			return;
		}
		if (safetyCheckerResult.getResultType() == ActualResultType.EXCEPTION_OR_ERROR) {
			setResultMessage("Error: " + safetyCheckerResult.getIResult().getLongDescription());
		} else if (getExpectedResult() == ExpectedResultType.NOANNOTATION) {
			setResultMessage("File was neither annotated nor does the filename contain a specification."
					+ "\tModel checker says: " + safetyCheckerResult.getResultType().toString());
		} else {
			setResultMessage("Annotation says: " + getExpectedResult() + "\tModel checker says: "
					+ safetyCheckerResult.getResultType().toString());
		}

		final IResult iResult = safetyCheckerResult.getIResult();
		if (iResult != null) {
			setResultMessage(getResultMessage() + "\t ShortDescription: " + iResult.getShortDescription());
			setResultMessage(getResultMessage() + "\t LongDescription: " + iResult.getLongDescription()
					.replace(System.getProperty("line.separator"), " ##NEWLINE## ").replace("\n", " ##NEWLINE## "));
		}

		// category: Plug-in, expected, actual
		setResultCategory(String.format("%s ## %s ## %s", mtoolIdentifier, getExpectedResult(),
				safetyCheckerResult.getResultType()));

		// statistics prefix:
		setResultMessage(
				String.format("%s ## %s ## %s ## %s ## %s", getExpectedResult(), safetyCheckerResult.getResultType(),
						mResultTime, mResultMemory, getResultMessage().replace("\n", "\n\t\t\t")));
	}

	private ActualResult getActualResult(final Collection<IResult> results) {
		final ActualResult returnValue;
		final Map<ActualResultType, ActualResult> resultSet = new HashMap<>();
		BenchmarkResult<?> benchmark = null;
		for (final IResult result : results) {
			if (result instanceof BenchmarkResult) {
				benchmark = (BenchmarkResult<?>) result;
			}
			final ActualResult extracted = extractResult(result);
			if (extracted != null) {
				resultSet.put(extracted.getResultType(), extracted);
			}
		}

		// only benchmark result: assume timeout~
		if (benchmark != null && results.size() == 1) {
			return new ActualResult(ActualResultType.TIMEOUT, benchmark);
		}

		if (resultSet.containsKey(ActualResultType.EXCEPTION_OR_ERROR)) {
			returnValue = resultSet.get(ActualResultType.EXCEPTION_OR_ERROR);
		} else if (resultSet.containsKey(ActualResultType.SYNTAX_ERROR)) {
			returnValue = resultSet.get(ActualResultType.SYNTAX_ERROR);
		} else if (resultSet.containsKey(ActualResultType.UNSUPPORTED_SYNTAX)) {
			returnValue = resultSet.get(ActualResultType.UNSUPPORTED_SYNTAX);
		} else if (resultSet.containsKey(ActualResultType.SAFE)) {
			returnValue = resultSet.get(ActualResultType.SAFE);
		} else if (resultSet.containsKey(ActualResultType.UNSAFE)) {
			returnValue = resultSet.get(ActualResultType.UNSAFE);
		} else if (resultSet.containsKey(ActualResultType.UNKNOWN)) {
			returnValue = resultSet.get(ActualResultType.UNKNOWN);
		} else if (resultSet.containsKey(ActualResultType.TIMEOUT)) {
			returnValue = resultSet.get(ActualResultType.TIMEOUT);
		} else {
			returnValue = resultSet.get(ActualResultType.NO_RESULT);
		}
		return returnValue;
	}

	private ActualResult extractResult(final IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			return new ActualResult(ActualResultType.SAFE, result);
		}

		if (result instanceof CounterExampleResult) {
			return new ActualResult(ActualResultType.UNSAFE, result);
		}

		if (result instanceof UnprovableResult) {
			return new ActualResult(ActualResultType.UNKNOWN, result);
		}

		if (result instanceof TypeErrorResult) {
			return new ActualResult(ActualResultType.SYNTAX_ERROR, result);
		}

		if (result instanceof SyntaxErrorResult) {
			return new ActualResult(ActualResultType.SYNTAX_ERROR, result);
		}

		if (result instanceof ITimeoutResult) {
			return new ActualResult(ActualResultType.TIMEOUT, result);
		}

		if (result instanceof UnsupportedSyntaxResult) {
			return new ActualResult(ActualResultType.UNSUPPORTED_SYNTAX, result);
		}

		if (result instanceof ExceptionOrErrorResult) {
			return new ActualResult(ActualResultType.EXCEPTION_OR_ERROR, result);
		}

		if (result instanceof NoResult) {
			return new ActualResult(ActualResultType.NO_RESULT, result);
		}

		return null;
	}

	@Override
	public boolean getJUnitSuccess(final TestResult actualResult) {
		// Matthias wants to see Unknown results as success, and so does Christopher
		switch (actualResult) {
		case FAIL:
		case UNKNOWN:
			return false;
		case SUCCESS:
			return true;
		default:
			throw new IllegalArgumentException("actualResult has an unknown value");
		}
	}
}
