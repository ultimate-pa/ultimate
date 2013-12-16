package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;


/**
 * Read the predefined expected result from the input file and compare
 * it to ULTIMATE's output
 * 
 * @author Jan Leike
 */
public class LassoRankerTestResultDecider implements ITestResultDecider {
	
	/**
	 * Types of results that can be specified by test examples
	 * 
	 * @author Jan Leike
	 */
	public enum ExpectedResult {
		IGNORE,
		TERMINATION,
		TERMINATIONDERIVABLE,
		NONTERMINATION,
		NONTERMINATIONDERIVABLE,
		UNKNOWN,
		ERROR,
		UNSPECIFIED
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
	 * Expected results are expected to be specified in an input file's
	 * first line and start with '//#r'.
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
			String expected = line.substring(4);
			switch (expected.toLowerCase()) {
				case "ignore":
					return ExpectedResult.IGNORE;
				case "termination":
					return ExpectedResult.TERMINATION;
				case "terminationderivable":
					return ExpectedResult.TERMINATIONDERIVABLE;
				case "nontermination":
					return ExpectedResult.NONTERMINATION;
				case "nonterminationderivable":
					return ExpectedResult.NONTERMINATIONDERIVABLE;
				case "unknown":
					return ExpectedResult.UNKNOWN;
				case "error":
					return ExpectedResult.ERROR;
			}
			return null;
		}
		if (line != null) {
			return ExpectedResult.UNSPECIFIED;
		}
		return null;
	}
	
	@Override
	public boolean isResultFail() {
		Logger logger = Logger.getLogger(LassoRankerTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = false;
		
		if (m_expected_result == null) {
			customMessages.add("Could not understand the specification of the "
					+ "results.");
			fail = true;
		} else if (m_expected_result == ExpectedResult.UNSPECIFIED) {
			customMessages.add("No expected results defined in the input file");
		} else {
			customMessages.add(m_expected_result.toString());
			Set<Entry<String, List<IResult>>> resultSet = UltimateServices
					.getInstance().getResultMap().entrySet();
			customMessages.add(resultSet.toString());
			// TODO: check result
		}
		
		Util.logResults(logger, m_input_file_name, fail, customMessages);
		return fail;
	}
}
