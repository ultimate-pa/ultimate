package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.*;
import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimatetest.decider.TestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Read the predefined expected result from the input file and compare it to
 * ULTIMATE's output
 * 
 * @author Jan Leike
 */
public class LassoRankerTestResultDecider extends TestResultDecider {

	/**
	 * Types of results that can be specified by test examples
	 * 
	 * @author Jan Leike
	 */
	public enum ExpectedResult {
		IGNORE, TERMINATION, TERMINATIONDERIVABLE, NONTERMINATION, NONTERMINATIONDERIVABLE, UNKNOWN, ERROR, UNSPECIFIED
	}

	private String m_input_file_name;
	private ExpectedResult m_expected_result;

	public LassoRankerTestResultDecider(File inputFile) {
		m_input_file_name = inputFile.getName();
		m_expected_result = checkExpectedResult(inputFile);
	}

	/**
	 * Return the expected result
	 */
	public ExpectedResult getExpectedResult() {
		return m_expected_result;
	}

	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's first
	 * line and start with '//#r'.
	 */
	private static ExpectedResult checkExpectedResult(File inputFile) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(inputFile));
			line = br.readLine();
			br.close();
		} catch (IOException e) {
			line = null;
		}
		if (line != null && line.startsWith("//#r")) {
			String expected = line.substring(4).toLowerCase();
			if (expected.equals("ignore")) {
				return ExpectedResult.IGNORE;
			} else if (expected.equals("termination")) {
				return ExpectedResult.TERMINATION;
			} else if (expected.equals("terminationderivable")) {
				return ExpectedResult.TERMINATIONDERIVABLE;
			} else if (expected.equals("nontermination")) {
				return ExpectedResult.NONTERMINATION;
			} else if (expected.equals("nonterminationderivable")) {
				return ExpectedResult.NONTERMINATIONDERIVABLE;
			} else if (expected.equals("unknown")) {
				return ExpectedResult.UNKNOWN;
			} else if (expected.equals("error")) {
				return ExpectedResult.ERROR;
			} else {
				return null;
			}
		}
		if (line != null) {
			return ExpectedResult.UNSPECIFIED;
		}
		return null;
	}

	@Override
	public TestResult getTestResult(IResultService resultService) {
		Logger logger = Logger.getLogger(LassoRankerTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = false;

		if (m_expected_result == null) {
			customMessages.add("Could not understand the specification of the " + "results.");
			fail = true;
		} else if (m_expected_result == ExpectedResult.UNSPECIFIED) {
			customMessages.add("No expected results defined in the input file");
		} else {
			customMessages.add("Expected Result: " + m_expected_result.toString());
			Map<String, List<IResult>> resultMap = resultService.getResults();
			List<IResult> results = resultMap.get(Activator.s_PLUGIN_ID);
			IResult lastResult = results.get(results.size() - 1);
			customMessages.add("Results: " + results.toString());

			switch (m_expected_result) {
			case TERMINATION:
				fail = lastResult instanceof NonTerminationArgumentResult;
				break;
			case TERMINATIONDERIVABLE:
				fail = !(lastResult instanceof TerminationArgumentResult);
				break;
			case NONTERMINATION:
				fail = lastResult instanceof TerminationArgumentResult;
				break;
			case NONTERMINATIONDERIVABLE:
				fail = !(lastResult instanceof NonTerminationArgumentResult);
				break;
			case UNKNOWN:
				fail = !(lastResult instanceof NoResult);
				break;
			case ERROR:
				fail = !(lastResult instanceof SyntaxErrorResult);
				break;
			default:
				fail = true;
				break;
			}
		}

		Util.logResults(logger, m_input_file_name, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(IResultService resultService, Throwable e) {
		return TestResult.FAIL;
	}

}
