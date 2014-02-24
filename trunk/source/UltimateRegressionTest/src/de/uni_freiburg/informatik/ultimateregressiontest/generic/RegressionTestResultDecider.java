package de.uni_freiburg.informatik.ultimateregressiontest.generic;

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
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;


//TODO: Make shared code base 

/**
 * This class is more or less a copy of the TraceAbstractionTestResultDecider, but without Summary Log.
 * 
 * 
 * 
 * @author dietsch
 *
 */
public class RegressionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	private ExpectedResult m_ExpectedResult;

	private enum ExpectedResult {
		SAFE, UNSAFE, NOSPECIFICATION, SYNTAXERROR, NOANNOTATION
	}

	public RegressionTestResultDecider(File inputFile) {
		m_InputFile = inputFile.getAbsolutePath();
		m_ExpectedResult = getExpectedResult(inputFile);
	}

	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's first
	 * line and start with '//#Unsafe', '//#Safe' or '//#NoSpec'. If this is not
	 * case, the expected result may be specified within the file name via the
	 * suffix "-safe" or "-unsafe".
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
			} else if (line.contains("#NoSpec")) {
				return ExpectedResult.NOSPECIFICATION;
			} else if (line.contains("#SyntaxError")) {
				return ExpectedResult.SYNTAXERROR;
			}
		}
		if (inputFile.getName().toLowerCase().contains("-safe") || inputFile.getName().toLowerCase().contains("_safe")) {
			return ExpectedResult.SAFE;
		} else if (inputFile.getName().toLowerCase().contains("-unsafe")
				|| inputFile.getName().toLowerCase().contains("_unsafe")) {
			return ExpectedResult.UNSAFE;
		}
		return ExpectedResult.NOANNOTATION;
	}

	@Override
	public boolean isResultFail() {
		Logger log = Logger.getLogger(RegressionTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		final boolean fail;
		List<IResult> traceAbstractionResults = new ArrayList<IResult>();
		
		for (Entry<String, List<IResult>> entry : UltimateServices.getInstance().getResultMap().entrySet()) {
			traceAbstractionResults.addAll(entry.getValue());
		}
		
		if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
			customMessages.add("Couldn't understand the specification of the file \"" + m_InputFile + "\".\n"
					+ "Use //#Safe or //#Unsafe to indicate that the program is safe resp. unsafe. Use "
					+ "//#NoSpec if there is still no decision about the specification.");
		}
		if (traceAbstractionResults.size() == 0) {
			fail = true;
			customMessages.add("There were no results at all. Therefore an exception has been thrown.");
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
				customMessages.add(String.format("Annotation says: %s\tModel checker says: %s", m_ExpectedResult,
						result));
			} else {
				if (result instanceof ExceptionOrErrorResult) {
					customMessages.add(String.format("Error: %s", result.getLongDescription()));
				} else if (result instanceof TimeoutResult) {
					customMessages.add("Unknown: Timeout");

				} else if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
					customMessages
							.add("Unknown: File was neither annotated nor does the filename contain a specification.");
				} else {
					customMessages.add(String.format("Error: Annotation says %s\tModel checker says %s",
							m_ExpectedResult, result.getShortDescription() != "" ? result.getShortDescription()
									: "NoResult"));
				}
			}
		}
		// Add benchmark results to TraceAbstraction summary
		BenchmarkResult benchmarkResult = getBenchmarkResultOfResultSet(traceAbstractionResults);
		if (benchmarkResult != null) {
			customMessages.add(benchmarkResult.getLongDescription());
		} else {
			customMessages.add("No benchmark results available.");
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
				if (((GenericResultAtElement<?>) res).getShortDescription() == "No specification checked"
						&& ((GenericResultAtElement<?>) res).getShortDescription() == "We were not able to verify any"
								+ " specifiation because the program does not contain any specification.") {
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
			} else if (res instanceof ExceptionOrErrorResult) {
				return res;
			}
		}
		return new NoResult(null, null, null);
	}

	public boolean isResultFail(Exception e) {
		Collection<String> customMessages = new LinkedList<String>();
		Logger log = Logger.getLogger(RegressionTestResultDecider.class);
		customMessages.add(String.format("Exception of type %s thrown.\tMessage: %s"  , e.getClass().getName(),e.getMessage()));
		Util.logResults(log, m_InputFile, true, customMessages);
		return true;
	}
}
