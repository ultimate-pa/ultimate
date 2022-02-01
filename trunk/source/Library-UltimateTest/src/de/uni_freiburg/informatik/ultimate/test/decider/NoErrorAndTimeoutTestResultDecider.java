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

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IFailedAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;

/**
 * The {@link NoErrorAndTimeoutTestResultDecider} will fail a test if an {@link IFailedAnalysisResult}, an
 * {@link ITimeoutResult} or a {@link TerminationAnalysisResult} with Unknown occurs. Every other result will be a
 * success.
 *
 * If the test is a success, the message will contain all result short descriptions except the ones of
 * {@link StatisticsResult}s.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NoErrorAndTimeoutTestResultDecider extends NoErrorTestResultDecider {

	/**
	 * The standard constructor for a test result decider. It takes an {@link UltimateRunDefinition} as argument.
	 */
	public NoErrorAndTimeoutTestResultDecider(final UltimateRunDefinition urd) {
		super(urd);
	}

	@Override
	protected boolean checkFailure(final IResult result) {
		if (super.checkFailure(result)) {
			return true;
		}
		if (result instanceof ITimeoutResult) {
			return true;
		}
		return false;
	}

}
