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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.Termination;
import de.uni_freiburg.informatik.ultimate.core.model.results.IFailedAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * The {@link NoErrorTestResultDecider} will fail a test if an {@link IFailedAnalysisResult} or a
 * {@link TerminationAnalysisResult} with Unknown occurs. Every other result will be a success.
 *
 * If the test is a success, the message will contain all result short descriptions except the ones of
 * {@link StatisticsResult}s.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NoErrorTestResultDecider extends TestResultDecider {

	private final String mInputFileNames;

	/**
	 * The standard constructor for a test result decider. It takes an {@link UltimateRunDefinition} as argument.
	 */
	public NoErrorTestResultDecider(final UltimateRunDefinition urd) {
		mInputFileNames = urd.getInputFileNames();
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {
		setResultCategory("");
		setResultMessage("");

		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(NoErrorTestResultDecider.class);
		LinkedHashSet<String> customMessages = new LinkedHashSet<>();

		boolean fail = false;
		final Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		for (final Entry<String, List<IResult>> x : resultSet) {
			for (final IResult result : x.getValue()) {
				if (checkFailure(result)) {
					setCategoryAndMessage(result);
					customMessages = new LinkedHashSet<>();
					customMessages.add(result.getShortDescription());
					fail = true;
					break;
				}
				if (result instanceof StatisticsResult<?>) {
					continue;
				}
				customMessages.add(result.getShortDescription());
			}
		}

		if (!fail) {
			final String msg = customMessages.stream().collect(Collectors.joining(", "));
			setResultCategory(msg);
			setResultMessage(msg);
		}
		TestUtil.logResults(log, mInputFileNames, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		setResultCategory("Unexpected exception");
		setResultMessage("Unexpected exception: " + e.getMessage());
		TestUtil.logResults(NoErrorTestResultDecider.class, mInputFileNames, true, new ArrayList<String>(), services);
		return TestResult.FAIL;
	}

	protected boolean checkFailure(final IResult result) {
		if (result instanceof IFailedAnalysisResult) {
			return true;
		}
		if (result instanceof TerminationAnalysisResult) {
			final TerminationAnalysisResult taresult = (TerminationAnalysisResult) result;
			if (taresult.getTermination() == Termination.UNKNOWN) {
				return true;
			}
		}
		return false;
	}

	private void setCategoryAndMessage(final IResult result) {
		setResultCategory(result.getShortDescription());
		setResultMessage(result.getLongDescription());
	}

}
