/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLFiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLInfiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.Termination;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public class LTLCheckerOverallResultEvaluator extends SafetyCheckerOverallResultEvaluator {

	private int mAllSaveCounter = 0;

	@Override
	protected SafetyCheckerOverallResult detectResultCategory(final IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			mAllSaveCounter++;
			if (mAllSaveCounter < 2) {
				return SafetyCheckerOverallResult.NO_RESULT;
			}
			return SafetyCheckerOverallResult.SAFE;
		} else if (result instanceof LTLInfiniteCounterExampleResult<?, ?, ?>) {
			return SafetyCheckerOverallResult.UNSAFE;
		} else if (result instanceof LTLFiniteCounterExampleResult<?, ?, ?>) {
			return SafetyCheckerOverallResult.UNSAFE;
		} else if (result instanceof TerminationAnalysisResult) {
			final TerminationAnalysisResult tar = (TerminationAnalysisResult) result;
			if (tar.getTermination() == Termination.UNKNOWN) {
				return SafetyCheckerOverallResult.UNKNOWN;
			}
		}
		return super.detectResultCategory(result);
	}
}
