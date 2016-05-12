/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimatetest.decider;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

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
	public TestResult getTestResult(IUltimateServiceProvider services) {
		final ILogger logger = services.getLoggingService().getLogger(LassoRankerTestResultDecider.class);
		final IResultService resultService = services.getResultService();
		final Collection<String> customMessages = new LinkedList<String>();
		boolean fail = false;

		String result = "";
		if (m_expected_result == null) {
			customMessages.add("Could not understand the specification of the " + "results.");
			fail = true;
		} else if (m_expected_result == ExpectedResult.UNSPECIFIED) {
			customMessages.add("No expected results defined in the input file");
		} else {
			Map<String, List<IResult>> resultMap = resultService.getResults();
			List<IResult> results = resultMap.get("de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker");
			if (results != null) {
				IResult lastResult = results.get(results.size() - 1);
				customMessages.add("Expected Result: " + m_expected_result.toString());
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
				result = lastResult.getClass().getSimpleName();
			} else {
				fail = true;
			}
		}

		setResultCategory(result + " (Expected: " + m_expected_result + ")");
		setResultMessage(customMessages.toString());
		TestUtil.logResults(logger, m_input_file_name, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider service, Throwable e) {
		return TestResult.FAIL;
	}

}
