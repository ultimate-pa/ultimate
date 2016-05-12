/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class NoTimeoutTestResultDecider extends TestResultDecider {

	private final String mInputFileNames;

	/**
	 * 
	 * @param inputFile
	 * @param settingsFile
	 * @param fileending
	 *            use .c or .bpl or something like that. The . is important
	 * 
	 */
	public NoTimeoutTestResultDecider(UltimateRunDefinition urd) {
		mInputFileNames = urd.getInputFileNames();
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services) {
		setResultCategory("");
		setResultMessage("");

		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(NoTimeoutTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<String>();
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

		TestUtil.logResults(log, mInputFileNames, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(IUltimateServiceProvider services, Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(NoTimeoutTestResultDecider.class, mInputFileNames, true, new ArrayList<String>(), services);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(IResult result, Collection<String> customMessages) {
		setResultCategory(result.getShortDescription());
		setResultMessage(result.getLongDescription());
		customMessages.add(result.getLongDescription());
	}

}
