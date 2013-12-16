package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
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
	private String m_input_file_name;
	private String m_expected_result;
	
	public static final String[] s_expected_results =
		{"Termination", "TerminationDerivable", "Nontermination", "Unknown",
		 "Error"};
	
	public LassoRankerTestResultDecider(File inputFile) {
		m_input_file_name = inputFile.getName();
		m_expected_result = getExpectedResult(inputFile);
	}
	
	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's
	 * first line and start with '//#r'.
	 */
	public static String getExpectedResult(File inputFile) {
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
			return line.substring(4);
		}
		return null;
	}
	
	@Override
	public boolean isResultFail() {
		Logger logger = Logger.getLogger(LassoRankerTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = false;
		
		Set<String> expected = new HashSet<String>();
		for (String result : s_expected_results) {
			expected.add(result);
		}
		
		if (m_expected_result == null) {
			customMessages.add("No expected results defined in the input file");
		} else {
			customMessages.add(m_expected_result);
			if (!expected.contains(m_expected_result)) {
				customMessages.add("Unknown expected result specified.");
				fail = true;
			}
			Set<Entry<String, List<IResult>>> resultSet = UltimateServices
					.getInstance().getResultMap().entrySet();
			customMessages.add(resultSet.toString());
			// TODO: check result
		}
		Util.logResults(logger, m_input_file_name, fail, customMessages);
		return fail;
	}

}
