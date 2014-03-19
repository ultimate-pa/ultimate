package de.uni_freiburg.informatik.ultimatetest;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Decide if Ultimate Automizer verified a program correctly.
 * 
 * @author Betim Musa, Matthias Heizmann
 *
 */
public class TraceAbstractionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	private ExpectedResult m_ExpectedResult;
	private TraceAbstractionTestSummary m_Summary;
	private String m_UniqueString;
	
	private enum TestOutcome {
		FAIL,
		UNKNOWN,
		SUCCESS
	}
	
	/**
	 * Result that we expect after checking filename and keywords of the input
	 * file.
	 */
	private enum ExpectedResult {
		SAFE,
		UNSAFE,
		SYNTAXERROR,
		NOANNOTATION
	}
	
	/**
	 * Result that is returned by the Automizer toolchain.
	 */
	private enum AutomizerResultType {
		SAFE,
		UNSAFE,
		UNKNOWN,
		SYNTAX_ERROR,
		TIMEOUT,
		UNSUPPORTED_SYNTAX,
		EXCEPTION_OR_ERROR,
		NO_RESULT;
	}
	
	private class AutomizerResult {
		private final IResult m_IResult;
		private final AutomizerResultType m_AutomizerResultType;
		public AutomizerResult(AutomizerResultType automizerResultType,
				IResult iResult) {
			super();
			m_IResult = iResult;
			m_AutomizerResultType = automizerResultType;
		}
		public IResult getIResult() {
			return m_IResult;
		}
		public AutomizerResultType getAutomizerResultType() {
			return m_AutomizerResultType;
		}
		
	}
	

	
	public TraceAbstractionTestResultDecider(File inputFile, 
			TraceAbstractionTestSummary testSummary,
			String uniqueString) {
		m_InputFile = inputFile.getAbsolutePath();
		m_ExpectedResult = getExpectedResult(inputFile);
		if (testSummary == null) {
			throw new ExceptionInInitializerError("summary may not be null");
		}
		m_Summary = testSummary;
		m_UniqueString = uniqueString;
	}
	
	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's
	 * first line and start with '//#Unsafe', '//#Safe' or '//#SyntaxError'.
	 * If this is not case, the expected result may be specified within the file name via the suffix
	 * "-safe" or "-unsafe".
	 */
	private static ExpectedResult getExpectedResult(File inputFile) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(inputFile));
			line = br.readLine();
			br.close();
		} catch (IOException e) {
			line = null;
		}
		if (line != null) {
			if (line.contains("#Safe")) {
				return ExpectedResult.SAFE;
			} else if (line.contains("#Unsafe")) {
				return ExpectedResult.UNSAFE;
			} else if (line.contains("#SyntaxError")) { 
				return ExpectedResult.SYNTAXERROR;
			}
		}
		if (inputFile.getName().toLowerCase().contains("-safe") ||
				inputFile.getName().toLowerCase().contains("_safe")) {
			return ExpectedResult.SAFE;
		} else if (inputFile.getName().toLowerCase().contains("-unsafe") || 
				inputFile.getName().toLowerCase().contains("_unsafe")) {
			return ExpectedResult.UNSAFE;
		}
		return ExpectedResult.NOANNOTATION;
	}
	

	@Override
	public boolean isResultFail() {
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		final TestOutcome testoutcome;
		List<IResult> traceAbstractionResults = new ArrayList<IResult>();
		for (Entry<String, List<IResult>> entry : UltimateServices.getInstance().getResultMap().entrySet()) {
			traceAbstractionResults.addAll(entry.getValue());
		}
		if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
			customMessages
			.add("Couldn't understand the specification of the file \"" + m_InputFile + "\".\n" +
			     "Use //#Safe or //#Unsafe to indicate that the program is safe resp. unsafe. Use "+
					"//#NoSpec if there is still no decision about the specification.");
		}
		String uniqueStringPrefixOfInputFile = m_UniqueString + "_" + m_InputFile;
		AutomizerResult automizerResult = getAutomizerResult(traceAbstractionResults);
		assert (automizerResult != null) : "if there is no result you should use NO_RESULT"; 
		switch (automizerResult.getAutomizerResultType()) {
		case EXCEPTION_OR_ERROR:
			testoutcome = TestOutcome.FAIL;
			break;
		case SAFE:
			if (m_ExpectedResult == ExpectedResult.SAFE) {
				testoutcome = TestOutcome.SUCCESS;
			} else if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
				testoutcome = TestOutcome.UNKNOWN;
			} else {
				testoutcome = TestOutcome.FAIL;
			}
			break;
		case UNSAFE:
			if (m_ExpectedResult == ExpectedResult.UNSAFE) {
				testoutcome = TestOutcome.SUCCESS;
			} else if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
				testoutcome = TestOutcome.UNKNOWN;
			} else {
				testoutcome = TestOutcome.FAIL;
			}
			break;
		case UNKNOWN:
			// syntax error should always have been found
			if (m_ExpectedResult == ExpectedResult.SYNTAXERROR) {
				testoutcome = TestOutcome.FAIL;
			} else {
				testoutcome = TestOutcome.UNKNOWN;
			}
			break;
		case SYNTAX_ERROR:
			if (m_ExpectedResult == ExpectedResult.SYNTAXERROR) {
				testoutcome = TestOutcome.SUCCESS;
			} else {
				testoutcome = TestOutcome.FAIL;
			}
			break;
		case TIMEOUT:
			// syntax error should always have been found
			if (m_ExpectedResult == ExpectedResult.SYNTAXERROR) {
				testoutcome = TestOutcome.FAIL;
			} else {
				testoutcome = TestOutcome.UNKNOWN;
			}
			break;
		case UNSUPPORTED_SYNTAX:
			testoutcome = TestOutcome.FAIL;
			break;
		case NO_RESULT:
			testoutcome = TestOutcome.FAIL;
			break;
		default:
			throw new AssertionError("unknown case");
		}

		String message;
		if (automizerResult.getAutomizerResultType() == AutomizerResultType.EXCEPTION_OR_ERROR) {
			message = "Error: " + automizerResult.getIResult().getLongDescription();
		} else if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
			message = "File was neither annotated nor does the filename contain a specification." + 
					"\tModel checker says: " + automizerResult.getAutomizerResultType().toString();
		} else {
			message = "Annotation says: " + m_ExpectedResult + 
					"\tModel checker says: " + automizerResult.getAutomizerResultType().toString();
		}

		IResult iResult = automizerResult.getIResult();
		if (iResult != null) {
			message += "\t ShortDescription: " + iResult.getShortDescription();
			message += "\t LongDescription: " + iResult.getLongDescription(); 
		}

		switch (testoutcome) {
		case FAIL:
			m_Summary.addFail(automizerResult.getAutomizerResultType().toString(), uniqueStringPrefixOfInputFile, message);
			break;
		case SUCCESS:
			m_Summary.addSuccess(automizerResult.getAutomizerResultType().toString(), uniqueStringPrefixOfInputFile, message);
			break;
		case UNKNOWN:
			m_Summary.addUnknown(automizerResult.getAutomizerResultType().toString(), uniqueStringPrefixOfInputFile, message);
			break;
		default:
			throw new AssertionError("unknown testoutcome");
		}

		// Add benchmark results to TraceAbstraction summary
		Collection<BenchmarkResult> bench = filterResults(traceAbstractionResults, BenchmarkResult.class);
		m_Summary.addTraceAbstractionBenchmarks(uniqueStringPrefixOfInputFile, bench);
		final boolean fail = (testoutcome == TestOutcome.FAIL);
		Util.logResults(log, m_InputFile, fail, customMessages);
		return fail;
	}

	/**
	 * Returns new Collections that contains all IResults from resCollection
	 * that are subclasses of the class resClass.
	 */
	private <E extends IResult> Collection<E> filterResults(
					Collection<IResult> resCollection, Class<E> resClass) {
		ArrayList<E> filteredList = new ArrayList<E>();
		for (IResult res : resCollection) {
			if (res.getClass().isAssignableFrom(resClass)) {
				@SuppressWarnings("unchecked")
				E benchmarkResult = (E) res;
				filteredList.add((E) benchmarkResult);
			}
		}
		return filteredList;
	}
	
	
	private AutomizerResult getAutomizerResult(List<IResult> results) {
		final AutomizerResult returnValue;
		Map<AutomizerResultType, AutomizerResult> resultSet = 
				new HashMap<AutomizerResultType, AutomizerResult>();
		for (IResult result : results) {
			AutomizerResult extracted = extractResult(result);
			if (extracted != null) {
				resultSet.put(extracted.getAutomizerResultType(), extracted);
			}
		}
		if (resultSet.containsKey(AutomizerResultType.EXCEPTION_OR_ERROR)) {
			returnValue = resultSet.get(AutomizerResultType.EXCEPTION_OR_ERROR);
		} else if (resultSet.containsKey(AutomizerResultType.SYNTAX_ERROR)) {
			if (resultSet.size() > 1) {
				throw new AssertionError("no other result allowed");
			} else {
				returnValue = resultSet.get(AutomizerResultType.SYNTAX_ERROR);
			}
		} else if (resultSet.containsKey(AutomizerResultType.UNSUPPORTED_SYNTAX)) {
			if (resultSet.size() > 1) {
				throw new AssertionError("no other result allowed");
			} else {
				returnValue = resultSet.get(AutomizerResultType.UNSUPPORTED_SYNTAX);
			}
		} else if (resultSet.containsKey(AutomizerResultType.SAFE)) {
			returnValue = resultSet.get(AutomizerResultType.SAFE);
		} else if (resultSet.containsKey(AutomizerResultType.UNSAFE)) {
			returnValue = resultSet.get(AutomizerResultType.UNSAFE);
		} else if (resultSet.containsKey(AutomizerResultType.UNKNOWN)) {
			returnValue = resultSet.get(AutomizerResultType.UNKNOWN);
		} else if (resultSet.containsKey(AutomizerResultType.TIMEOUT)) {
			returnValue = resultSet.get(AutomizerResultType.TIMEOUT);
		} else {
			returnValue = resultSet.get(AutomizerResultType.NO_RESULT);
		}
		return returnValue;
	}
	

	private AutomizerResult extractResult(IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			return new AutomizerResult(AutomizerResultType.SAFE, result);
		} else if (result instanceof CounterExampleResult) {
			return new AutomizerResult(AutomizerResultType.UNSAFE, null);
		} else if (result instanceof UnprovableResult) {
			return new AutomizerResult(AutomizerResultType.UNKNOWN, null);
		} else if (result instanceof TypeErrorResult) {
			return new AutomizerResult(AutomizerResultType.SYNTAX_ERROR, result);
		} else if (result instanceof SyntaxErrorResult) {
			return new AutomizerResult(AutomizerResultType.SYNTAX_ERROR, result);
		} else if (result instanceof ITimeoutResult) {
			return new AutomizerResult(AutomizerResultType.TIMEOUT, null);
		} else if (result instanceof UnsupportedSyntaxResult) {
			return new AutomizerResult(AutomizerResultType.UNSUPPORTED_SYNTAX, result);
		} else if (result instanceof ExceptionOrErrorResult) {
			return new AutomizerResult(AutomizerResultType.EXCEPTION_OR_ERROR, result);
		} else {
			return null;
		}
	}
	


	public boolean isResultFail(Exception e) {
		m_Summary.addFail(
				AutomizerResultType.EXCEPTION_OR_ERROR.toString(), 
				m_InputFile, 
				"Exception of type " + e.getClass().getName() + " thrown.\t"+ "Message: " + e.getMessage());
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Util.logResults(log, m_InputFile, true, new LinkedList<String>());
		return true;
	}
	
	
}
