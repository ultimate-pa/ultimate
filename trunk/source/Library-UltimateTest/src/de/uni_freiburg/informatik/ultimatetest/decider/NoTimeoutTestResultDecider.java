package de.uni_freiburg.informatik.ultimatetest.decider;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class NoTimeoutTestResultDecider extends TestResultDecider {

	private final String mInputFile;

	/**
	 * 
	 * @param inputFile
	 * @param settingsFile
	 * @param fileending
	 *            use .c or .bpl or something like that. The . is important
	 * 
	 */
	public NoTimeoutTestResultDecider(UltimateRunDefinition urd) {
		mInputFile = urd.getInput().getAbsolutePath();
	}

	@Override
	public TestResult getTestResult(IResultService resultService) {

		setResultCategory("");
		setResultMessage("");

		Logger log = Logger.getLogger(NoTimeoutTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		customMessages.add("Expecting results to not contain TimeoutResult or ExceptionOrErrorResult");
		boolean fail = false;
		Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (Entry<String, List<IResult>> x : resultSet) {
			for (IResult result : x.getValue()) {
				if (result instanceof ExceptionOrErrorResult) {
					setCategoryAndMessageAndCustomMessage(result, customMessages);
					fail = true;
					break;
				} else if (result instanceof TimeoutResult) {
					setCategoryAndMessageAndCustomMessage(result, customMessages);
					fail = true;
					break;
				} else if (result instanceof TimeoutResultAtElement<?>) {
					setCategoryAndMessageAndCustomMessage(result, customMessages);
					fail = true;
					break;
				}
			}
		}

		if (!fail) {
			setResultCategory("Success");
			setResultMessage("");
		}

		TestUtil.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(IResultService resultService, Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(Logger.getLogger(NoTimeoutTestResultDecider.class), mInputFile, true,
				new ArrayList<String>(), resultService);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(IResult result, Collection<String> customMessages) {
		setResultCategory(result.getShortDescription());
		setResultMessage(result.getLongDescription());
		customMessages.add(result.getLongDescription());
	}

}