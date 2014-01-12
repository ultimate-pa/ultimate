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
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

public class TraceAbstractionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	private ExpectedResult m_ExpectedResult;
	private TraceAbstractionTestSummary m_Summary;
	private String m_ShortDescription = "Ultimate Automizer runtime statistics";
	private String m_SeqInLongDescr = "Ultimate Automizer took ";
	private enum ExpectedResult {
		SAFE,
		UNSAFE,
		NOSPECIFICATION,
		NOANNOTATION
	}
	public TraceAbstractionTestResultDecider(File inputFile, TraceAbstractionTestSummary testSummary) {
		m_InputFile = inputFile.getAbsolutePath();
		m_ExpectedResult = getExpectedResult(inputFile);
		if (testSummary == null) {
			throw new ExceptionInInitializerError("summary may not be null");
		}
		m_Summary = testSummary;
	}
	
	/**
	 * Read the expected result from an input file
	 * 
	 * Expected results are expected to be specified in an input file's
	 * first line and start with '//#Unsafe', '//#Safe' or '//#NoSpec'.
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
			} else {
				return ExpectedResult.NOANNOTATION;
			}
		}
		return ExpectedResult.NOANNOTATION;
	}
	
	@Override
	public boolean isResultFail() {
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = true;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();
		if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
			customMessages
			.add("Couldn't understand the specification of the file \"" + m_InputFile + "\".\n" +
			     "Use //#Safe or //#Unsafe to indicate that the program is safe resp. unsafe. Use "+
					"//#NoSpec if there is still no decision about the specification.");
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
			case NOSPECIFICATION:
				fail = resultSetContainsGenericResultWithNoSpecification(resultSet);
			}
			if (!fail) {
				String annotationAndModelCheckerResult = m_ExpectedResult == ExpectedResult.SAFE ?  "\"SAFE\"" : 
					(m_ExpectedResult == ExpectedResult.UNSAFE ? "\"UNSAFE\"" : "\"NoSpecification\""); 
				m_Summary.addSuccess(result, m_InputFile, "Annotation says: " + annotationAndModelCheckerResult + 
						"\tModel checker says: " + annotationAndModelCheckerResult);
			} else {
				if (m_ExpectedResult == ExpectedResult.NOANNOTATION) {
					m_Summary.addUnknown(result, m_InputFile, "File wasn't annotated.");
				} else {
					m_Summary.addFail(result, m_InputFile, (m_ExpectedResult == ExpectedResult.SAFE ? 
							"Annotation says: \"SAFE\" \t Model checker says: \"UNSAFE\"" :
							(m_ExpectedResult == ExpectedResult.UNSAFE ? 	
							"Annotation says: \"UNSAFE\" \t Model checker says: \"SAFE\"" :
							"Annotation says: \"NOSPEC\" \t Model checker says something else.")));
				}
				
			}
		}
		Util.logResults(log, m_InputFile, fail, customMessages);
		return fail;
	}
	private boolean resultSetContainsGenericResultWithNoSpecification(Set<Entry<String, List<IResult>>> resultSet) {
		for (Entry<String, List<IResult>> entry : resultSet) {
			for (IResult res : entry.getValue()) {
				if (res instanceof GenericResult) {
					if (((GenericResult<?>)res).getShortDescription() == "No specification checked" &&
							((GenericResult<?>)res).getShortDescription() == "We were not able to verify any" +
									" specifiation because the program does not contain any specification.") {
						return true;
					}
				}
			}
		}
		return false;
	}

	// TODO: Ensure that null can't be returned, or handle this case in the calling method.
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
