package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.ThrowableResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

public class TraceAbstractionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	private ExpectedResult m_ExpectedResult;
	private TraceAbstractionTestSummary m_Summary;
	private String m_UniqueString;
	
	private enum ExpectedResult {
		SAFE,
		UNSAFE,
		NOSPECIFICATION,
		SYNTAXERROR,
		NOANNOTATION
	}
	public TraceAbstractionTestResultDecider(File inputFile, TraceAbstractionTestSummary testSummary,
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
	 * first line and start with '//#Unsafe', '//#Safe' or '//#NoSpec'.
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
			} else if (line.contains("#NoSpec"))  {
				return ExpectedResult.NOSPECIFICATION;
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
		final boolean fail;
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
		if (traceAbstractionResults.size() == 0) {
			fail = true;
			customMessages
					.add("There were no results. Therefore an exception has been thrown.");
			m_Summary.addFail(null, uniqueStringPrefixOfInputFile, "Error: There were no results at all. "+
																	"Tool didn't exit normally.");
		} else {
			IResult result = getTraceAbstractionResultOfSet(traceAbstractionResults);
			switch (m_ExpectedResult) {
			case SAFE:
				fail = !(result instanceof PositiveResult);
				break;
			case UNSAFE:
				fail = !(result instanceof CounterExampleResult);
				break;
			case NOSPECIFICATION:
				fail = resultSetContainsGenericResultWithNoSpecification(traceAbstractionResults);
				break;
			case SYNTAXERROR:
				fail = !(result instanceof SyntaxErrorResult);
				break;
			case NOANNOTATION:
				fail = true;
				break;
			default:
				throw new AssertionError("unexpected case");
			}
			if (!fail) {
				m_Summary.addSuccess(result, uniqueStringPrefixOfInputFile, "Annotation says: " + m_ExpectedResult + 
						"\tModel checker says: " + m_ExpectedResult);
			} else {
				if (result instanceof ThrowableResult) {
					m_Summary.addFail(result, uniqueStringPrefixOfInputFile, "Error: " + result.getLongDescription());
				} else if (result instanceof TimeoutResult) {
					m_Summary.addUnknown(result, uniqueStringPrefixOfInputFile, "Annotation says: " + m_ExpectedResult +
							"\tModel checker says: Time out");
				} else if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
					m_Summary.addUnknown(result, uniqueStringPrefixOfInputFile, "File was neither annotated nor does the filename contain a specification.");
				} else {
					m_Summary.addFail(result, uniqueStringPrefixOfInputFile, "Annotation says: " + m_ExpectedResult + 
							"\tModel checker says: " + (result.getShortDescription() != "" ? result.getShortDescription() : "NoResult"));
				}
			}
		}
		// Add benchmark results to TraceAbstraction summary
		BenchmarkResult benchmarkResult = getBenchmarkResultOfResultSet(traceAbstractionResults);
		if (benchmarkResult != null) {
			m_Summary.addTraceAbstractionBenchmarks(uniqueStringPrefixOfInputFile, benchmarkResult.getLongDescription());
		} else {
			m_Summary.addTraceAbstractionBenchmarks(uniqueStringPrefixOfInputFile, "No benchmark results available.");
		}
		Util.logResults(log, m_InputFile, fail, customMessages);
		return fail;
	}
	
	private BenchmarkResult getBenchmarkResultOfResultSet(List<IResult> results) {
		for (IResult res : results) {
			if (res instanceof BenchmarkResult) {
				return ((BenchmarkResult) res); 
			}
		}
		return null;
	}
	
	private boolean resultSetContainsGenericResultWithNoSpecification(List<IResult> results) {
		for (IResult res : results) {
			if (res instanceof GenericResultAtElement) {
				if (((GenericResultAtElement<?>)res).getShortDescription() == "No specification checked" &&
						((GenericResultAtElement<?>)res).getShortDescription() == "We were not able to verify any" +
						" specifiation because the program does not contain any specification.") {
					return true;
				}
			}
		}
		return false;
	}
	

	private IResult getTraceAbstractionResultOfSet(List<IResult> results) {
		for (IResult res : results) {
			if (res instanceof PositiveResult) {
				return res;
			} else if (res instanceof CounterExampleResult) {
				return res;
			} else if (res instanceof TimeoutResult) {
				return res;
			} else if (res instanceof SyntaxErrorResult) {
				return res;
			} else if (res instanceof NoResult) {
				return res;
			} else if (res instanceof ThrowableResult) {
				return res;
			}
		}
		return new NoResult(null, null, null, null);
	}
	
	public boolean isResultFail(Exception e) {
		m_Summary.addFail(new NoResult(null, null, null, null), m_InputFile, "Exception of type " + e.getClass().getName() + " thrown.\t"+
		                                       "Message: " + e.getMessage());
		m_Summary.addTraceAbstractionBenchmarks(m_InputFile, "No benchmark results available.");
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Util.logResults(log, m_InputFile, true, new LinkedList<String>());
		return true;
	}
	
	
}
