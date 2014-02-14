package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

class TranslationTestResultDecider implements ITestResultDecider {

	private String mInputFile;

	public TranslationTestResultDecider(String inputFile) {
		mInputFile = inputFile;
	}

	@Override
	public boolean isResultFail() {

		Logger log = Logger.getLogger(TranslationTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		customMessages
				.add("Expecting results to not contain SyntaxErrorResult");
		boolean fail = false;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices
				.getInstance().getResultMap().entrySet();
		if (resultSet.size() == 0) {
			customMessages
					.add("There were no results (this is good for this test)");
		} else {
			for (Entry<String, List<IResult>> x : resultSet) {
				for (IResult result : x.getValue()) {
					customMessages.add(String.format("Result %s: %s", result.getShortDescription(),result.getLongDescription()));
					if (result instanceof SyntaxErrorResult) {
						fail = true;
					}
				}
			}
		}
		Util.logResults(log, mInputFile, fail, customMessages);
		return fail;
	}
	
	@Override
	public boolean isResultFail(Exception e) {
		return true;
	}

}