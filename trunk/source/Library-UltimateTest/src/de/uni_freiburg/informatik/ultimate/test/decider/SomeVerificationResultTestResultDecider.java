/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.Termination;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * The {@link SomeVerificationResultTestResultDecider} considers a run a
 * Success if some verification result was provided.
 * Expected results of files are not considered.
 *
 * If the test is a success, the message will contain all result short descriptions except the ones of
 * {@link StatisticsResult}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SomeVerificationResultTestResultDecider extends TestResultDecider {

	private final String mInputFileNames;

	/**
	 * The standard constructor for a test result decider. It takes an {@link UltimateRunDefinition} as argument.
	 */
	public SomeVerificationResultTestResultDecider(final UltimateRunDefinition urd) {
		mInputFileNames = urd.getInputFileNames();
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {
		setResultCategory("");
		setResultMessage("");

		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(SomeVerificationResultTestResultDecider.class);
		final LinkedHashSet<String> customMessages = new LinkedHashSet<>();

		boolean fail = true;
		final Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (final Entry<String, List<IResult>> x : resultSet) {
			for (final IResult result : x.getValue()) {
				if (checkSuccess(result)) {
					setCategoryAndMessage(result);
					customMessages.add(result.getShortDescription());
					fail = false;
					break;
				}
				if (result instanceof StatisticsResult<?>) {
					continue;
				}
				customMessages.add(result.getShortDescription());
				if (result instanceof TimeoutResult) {
					customMessages.add(result.getLongDescription());
				}
			}
		}

		final String msg = customMessages.stream().collect(Collectors.joining(", "));
		if (fail) {
			setResultCategory("NOT_SUCCESS");
		} else {
			setResultCategory(msg);
		}
		setResultMessage(msg);
		TestUtil.logResults(log, mInputFileNames, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(SomeVerificationResultTestResultDecider.class, mInputFileNames, true, new ArrayList<String>(), services);
		return TestResult.FAIL;
	}

	private static boolean checkSuccess(final IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			return true;
		}
		if (result instanceof CounterExampleResult) {
			return true;
		}

		if (result instanceof TerminationAnalysisResult) {
			final TerminationAnalysisResult taresult = (TerminationAnalysisResult) result;
			return (taresult.getTermination() != Termination.UNKNOWN);
		}
		return false;
	}

	private void setCategoryAndMessage(final IResult result) {
		setResultCategory(result.getShortDescription());
		setResultMessage(result.getLongDescription());
	}

}
