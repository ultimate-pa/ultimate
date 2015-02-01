/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.decider.TestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Took stuff from the old SafetyCheckTestResultDecider_OldVersion
 * 'cause there was so much I had to adjust for my own needs and
 * I don't want to dig into the new one to see if it suits me better
 * @author Christopher Dillo
 */
public class AbstractInterpretationTestResultDecider extends TestResultDecider {
	
	public enum ExpectedResultType {
		SAFE, UNSAFE, SYNTAXERROR, NOANNOTATION
	}
	
	protected enum ActualResultType {
		SAFE, UNSAFE, UNKNOWN, SYNTAX_ERROR, TIMEOUT, UNSUPPORTED_SYNTAX, EXCEPTION_OR_ERROR, NO_RESULT;
	}
	protected class ActualResult {
		private final IResult m_IResult;
		private final ActualResultType m_actualResultType;
		public ActualResult(ActualResultType automizerResultType, IResult iResult) {
			m_IResult = iResult;
			m_actualResultType = automizerResultType;
		}
		public IResult getIResult() {
			return m_IResult;
		}
		public ActualResultType getResultType() {
			return m_actualResultType;
		}
	}
	
	private String m_inputFile;
	
	private String m_toolIdentifier;
	
	private ExpectedResultType m_expectedResult;

	private Collection<IResult> m_results;

	/** Peak memory in MiB **/
	private String m_resultMemory = "";
	/** Runtime in ms **/
	private String m_resultTime = "";
	
	/**
	 * @param inputFile Well duh ;-)
	 * @param toolIdentifier Used to identify which tool the result belongs to.
	 */
	public AbstractInterpretationTestResultDecider(File inputFile, String toolIdentifier) {
		super();
		m_inputFile = inputFile.getAbsolutePath();
		m_toolIdentifier = toolIdentifier;
		generateExpectedResult(inputFile);
	}


	@Override
	public TestResult getTestResult(IResultService resultService) {
		Logger log = Logger.getLogger(AbstractInterpretationTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		final TestResult testoutcome;
		m_results = new ArrayList<IResult>();
		for (Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			m_results.addAll(entry.getValue());
		}

		// get benchmark result stuff
		for (IResult r : m_results) {
			if (r instanceof BenchmarkResult) {
				BenchmarkResult<?> br = (BenchmarkResult<?>) r;
				ICsvProviderProvider<?> ic = br.getBenchmark();
				
				if (ic instanceof Benchmark) {
					Benchmark benchmark = (Benchmark) ic;
					
					long memory = 0; // in bytes
					double time = 0; // in milliseconds
					
					for (String title : benchmark.getTitles()) {
						long watchMem = benchmark.getStartHeapSize(title) + benchmark.getPeakMemoryConsumed(title);
						if (watchMem > memory)
							memory = watchMem;
						time += benchmark.getElapsedTime(title, TimeUnit.MILLISECONDS);
					}
					
					m_resultMemory = String.format("%d", (memory / 1024 / 1024)); // -> MiB
					m_resultTime = String.format("%.0f", time);
				}
			}
		}

		ExpectedResultType expected = getExpectedResult();
		if (expected != null) {
			customMessages.add("Expected Result: " + expected);
		}

		if (expected == ExpectedResultType.NOANNOTATION) {
			customMessages.add("Couldn't understand the specification of the file \"" + m_inputFile + "\".");
		}
		ActualResult scResult = getActualResult(m_results);
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
		Util.logResults(log, m_inputFile, !getJUnitSuccess(testoutcome), customMessages, resultService);
		return testoutcome;
	}

	@Override
	public TestResult getTestResult(IResultService resultService, Throwable e) {
		generateResultMessageAndCategory(new ActualResult(ActualResultType.EXCEPTION_OR_ERROR,
				new ExceptionOrErrorResult("Ultimate", e)));
		Logger log = Logger.getLogger(AbstractInterpretationTestResultDecider.class);
		Util.logResults(log, m_inputFile, true, new LinkedList<String>(), resultService);
		return TestResult.FAIL;
	}

	protected void generateExpectedResult(File inputFile) {
		if (getExpectedResult() == null) {
			setExpectedResult(getExpectedResult(inputFile));
		}
	}
	
	public static ExpectedResultType getExpectedResult(File inputFile) {
		String line = Util.extractFirstLine(inputFile);
		if (line != null) {
			if (line.contains("#Safe") || line.contains("iSafe")) {
				return ExpectedResultType.SAFE;
			} else if (line.contains("#Unsafe") || line.contains("iUnsafe")) {
				return ExpectedResultType.UNSAFE;
			} else if (line.contains("#SyntaxError")) {
				return ExpectedResultType.SYNTAXERROR;
			}
		}
		String lowercaseFilename = inputFile.getName().toLowerCase();
		if (lowercaseFilename.contains("-safe") 
				|| lowercaseFilename.contains("_safe")
				|| lowercaseFilename.contains("true-unreach-call")){
			return ExpectedResultType.SAFE;
		} else if (lowercaseFilename.contains("-unsafe")
				|| lowercaseFilename.contains("_unsafe")
				|| lowercaseFilename.contains("false-unreach-call")){
			return ExpectedResultType.UNSAFE;
		}
		return ExpectedResultType.NOANNOTATION;
	}
	
	protected ExpectedResultType getExpectedResult() {
		return m_expectedResult;
	}
	
	protected void setExpectedResult(ExpectedResultType expectedResult) {
		m_expectedResult = expectedResult;
	}
	
	/**
	 * Message: Symbol for the LaTeX table denoting the expected result.
	 */
	protected void generateResultMessageAndCategory(ActualResult safetyCheckerResult) {
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

		IResult iResult = safetyCheckerResult.getIResult();
		if (iResult != null) {
			setResultMessage(getResultMessage() + "\t ShortDescription: " + iResult.getShortDescription());
			setResultMessage(getResultMessage() + "\t LongDescription: "
					+ iResult.getLongDescription().replace(System.getProperty("line.separator"), " ##NEWLINE## ").replace("\n", " ##NEWLINE## "));
		}
		
		// category: Plug-in, expected, actual
		setResultCategory(String.format("%s ## %s ## %s",
				m_toolIdentifier,
				getExpectedResult(),
				safetyCheckerResult.getResultType()));
		
		// statistics prefix:
		setResultMessage(String.format("%s ## %s ## %s ## %s ## %s",
				getExpectedResult(),
				safetyCheckerResult.getResultType(),
				m_resultTime,
				m_resultMemory,
				getResultMessage().replace("\n", "\n\t\t\t")));
	}

	private ActualResult getActualResult(Collection<IResult> results) {
		final ActualResult returnValue;
		Map<ActualResultType, ActualResult> resultSet = new HashMap<ActualResultType, ActualResult>();
		BenchmarkResult<?> benchmark = null;
		for (IResult result : results) {
			if (result instanceof BenchmarkResult)
				benchmark = (BenchmarkResult<?>) result;
			ActualResult extracted = extractResult(result);
			if (extracted != null) {
				resultSet.put(extracted.getResultType(), extracted);
			}
		}
		
		// only benchmark result: assume timeout~
		if ((benchmark != null) && results.size() == 1)
			return new ActualResult(ActualResultType.TIMEOUT, benchmark);
			
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

	private ActualResult extractResult(IResult result) {
		if (result instanceof AllSpecificationsHoldResult)
			return new ActualResult(ActualResultType.SAFE, result);
		
		if (result instanceof CounterExampleResult)
			return new ActualResult(ActualResultType.UNSAFE, result);
		
		if (result instanceof UnprovableResult)
			return new ActualResult(ActualResultType.UNKNOWN, result);
		
		if (result instanceof TypeErrorResult)
			return new ActualResult(ActualResultType.SYNTAX_ERROR, result);
		
		if (result instanceof SyntaxErrorResult)
			return new ActualResult(ActualResultType.SYNTAX_ERROR, result);
		
		if (result instanceof ITimeoutResult)
			return new ActualResult(ActualResultType.TIMEOUT, result);
		
		if (result instanceof UnsupportedSyntaxResult)
			return new ActualResult(ActualResultType.UNSUPPORTED_SYNTAX, result);
		
		if (result instanceof ExceptionOrErrorResult)
			return new ActualResult(ActualResultType.EXCEPTION_OR_ERROR, result);

		if (result instanceof NoResult)
			return new ActualResult(ActualResultType.NO_RESULT, result);

		return null;
	}


	@Override
	public boolean getJUnitSuccess(TestResult actualResult) {
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
