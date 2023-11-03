/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcSatResult;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcUnsatResult;

public class ChcOverallResultEvaluator implements IOverallResultEvaluator<ChcOverallResult> {

	private ChcOverallResult mOverallResult;
	private final Set<IResult> mMostSignificantResults = new HashSet<>();

	@Override
	public void evaluateOverallResult(final IResultService resultService) {
		ChcSatResult satResult = null;
		ChcUnsatResult unsatResult = null;
		TimeoutResult timeoutResult = null;
		ExceptionOrErrorResult errorResult = null;
		for (final Entry<String, List<IResult>> en : resultService.getResults().entrySet()) {
			for (final IResult res : en.getValue()) {
				if (res instanceof ChcSatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					satResult = (ChcSatResult) res;
					mMostSignificantResults.add(res);
				} else if (res instanceof ChcUnsatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					unsatResult = (ChcUnsatResult) res;
					mMostSignificantResults.add(res);
				} else if (res instanceof TimeoutResult) {
					timeoutResult = (TimeoutResult) res;
					mMostSignificantResults.add(res);
				} else if (res instanceof ExceptionOrErrorResult) {
					errorResult = (ExceptionOrErrorResult) res;
					mMostSignificantResults.add(res);
				}
			}
		}

		if (satResult != null) {
			mOverallResult = ChcOverallResult.SAT;
		} else if (unsatResult != null) {
			mOverallResult = ChcOverallResult.UNSAT;
		} else if (errorResult != null) {
			mOverallResult = ChcOverallResult.CRASH;
		} else if (timeoutResult != null) {
			mOverallResult = ChcOverallResult.TIMEOUT;
		} else {
			mOverallResult = ChcOverallResult.UNKNOWN;
		}
	}

	@Override
	public ChcOverallResult getOverallResult() {
		assert mOverallResult != null;
		return mOverallResult;
	}

	@Override
	public String generateOverallResultMessage() {
		return "most significant results: " + mMostSignificantResults;
	}

	@Override
	public Set<IResult> getMostSignificantResults() {
		return mMostSignificantResults;
	}

}
