package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

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
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

public class TraceAbstractionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	private ExpectedResult m_ExpectedResult;
	private enum ExpectedResult {
		SAFE,
		UNSAFE,
		UNSPECIFIED
	}
	public TraceAbstractionTestResultDecider(File inputFile) {
		m_InputFile = inputFile.getAbsolutePath();
		m_ExpectedResult = getExpectedResult(inputFile);
	}
	
	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's
	 * first line and start with '//#mUnsafe' or '//#mSafe'.
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
			if (line.contains("#mSafe") || line.contains("#iSafe")) {
				return ExpectedResult.SAFE;
			} else if (line.contains("#mUnsafe") || line.contains("#iUnsafe")) {
				return ExpectedResult.UNSAFE;
			} else {
				return ExpectedResult.UNSPECIFIED;
			}
		}
		return ExpectedResult.UNSPECIFIED;
	}
	
	@Override
	public boolean isResultFail() {
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = true;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();
		if (m_ExpectedResult == ExpectedResult.UNSPECIFIED) {
			customMessages
			.add("Couldn't understand the specification of the file \"" + m_InputFile + "\".\n" +
			     "Use \"//#mSafe\" or \"//#mUnsafe\" to indicate that the program is safe resp. unsafe.");
		}
		if (resultSet.size() == 0) {
			customMessages
					.add("There were no results. Therefore an exception has been thrown.");
		} else {
			IResult result = getResultOfSet(resultSet);
			switch (m_ExpectedResult) {
			case SAFE:
				fail = !(result instanceof PositiveResult);
				break;
			case UNSAFE:
				fail = !(result instanceof CounterExampleResult);
				break;
			case UNSPECIFIED:
				customMessages.add("Result of TraceAbstraction: " + result.toString());
				fail = true;
			}
		}
		Util.logResults(log, m_InputFile, fail, customMessages);
		return fail;
	}

	private IResult getResultOfSet(Set<Entry<String, List<IResult>>> resultSet) {
		for (Entry<String, List<IResult>> entry : resultSet) {
			for (IResult res : entry.getValue()) {
				if (res instanceof PositiveResult) {
					return res;
				} else if (res instanceof CounterExampleResult) {
					return res;
				} else if (res instanceof TimeoutResult) {
					return res;
				}
			}
		}
		return null;
	}
}
