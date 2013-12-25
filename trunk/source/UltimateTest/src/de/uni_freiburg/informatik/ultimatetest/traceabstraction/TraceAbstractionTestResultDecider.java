package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

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
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

public class TraceAbstractionTestResultDecider implements ITestResultDecider {
	private String m_InputFile;
	public TraceAbstractionTestResultDecider(String inputFile) {
		m_InputFile = inputFile;
	}
	
	@Override
	public boolean isResultFail() {
		Logger log = Logger.getLogger(TraceAbstractionTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		boolean fail = true;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();
		if (resultSet.size() == 0) {
			customMessages
					.add("There were no results. Therefore an exception has been thrown.");
		} else {
			for (Entry<String, List<IResult>> x : resultSet) {
				for (IResult result : x.getValue()) {
					if (result instanceof PositiveResult) {
						fail = false;
						break;
					} else if (result instanceof CounterExampleResult) {
						fail = false;
						break;
						// TODO: Check whether the file is unSafe.
					}
					// (musab): If the result is  neither an instance of PositiveResult nor an
					// instance of CounterExampleResult, then the test case is categorized as "failed".
				}
			}
		}
		Util.logResults(log, m_InputFile, fail, customMessages);
		return fail;
	}

}
