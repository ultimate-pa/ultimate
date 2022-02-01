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
package de.uni_freiburg.informatik.ultimate.test.decider;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * This {@link ITestResultDecider} will fail a test if a timeout or an exception occurs. Every other result will be a
 * success.
 *
 * This decider can be used for testing translation or preprocessing steps where no verification result is produced.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NoTimeoutTestResultDecider extends TestResultDecider {

	private final String mInputFileNames;

	/**
	 * The standard constructor for a test result decider. It takes an {@link UltimateRunDefinition} as argument.
	 */
	public NoTimeoutTestResultDecider(final UltimateRunDefinition urd) {
		mInputFileNames = urd.getInputFileNames();
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {
		setResultCategory("");
		setResultMessage("");

		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(NoTimeoutTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<>();
		customMessages.add("Expecting results to not contain TimeoutResult or ExceptionOrErrorResult");
		boolean fail = false;
		final Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (final Entry<String, List<IResult>> x : resultSet) {
			for (final IResult result : x.getValue()) {
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
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(NoTimeoutTestResultDecider.class, mInputFileNames, true, new ArrayList<String>(), services);
		return TestResult.FAIL;
	}

	private void setCategoryAndMessageAndCustomMessage(final IResult result, final Collection<String> customMessages) {
		setResultCategory(result.getShortDescription());
		setResultMessage(result.getLongDescription());
		customMessages.add(result.getLongDescription());
	}

}
