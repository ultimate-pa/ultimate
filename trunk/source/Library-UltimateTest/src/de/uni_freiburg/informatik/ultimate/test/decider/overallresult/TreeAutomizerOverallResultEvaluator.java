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

import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerSatResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerUnsatResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;

public class TreeAutomizerOverallResultEvaluator implements IOverallResultEvaluator<TreeAutomizerOverallResult> {

	private TreeAutomizerOverallResult mOverallResult;
	private final Set<IResult> mMostSignificatResults = new HashSet<>();

	@Override
	public void evaluateOverallResult(IResultService resultService) {
		TreeAutomizerSatResult satResult = null;
		TreeAutomizerUnsatResult unsatResult = null;
		TimeoutResult timeoutResult = null;
		for (Entry<String, List<IResult>> en : resultService.getResults().entrySet()) {
			for (IResult res : en.getValue()) {
				if (res instanceof TreeAutomizerSatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					satResult = (TreeAutomizerSatResult) res;
					mMostSignificatResults.add(res);
				} else if (res instanceof TreeAutomizerUnsatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					unsatResult = (TreeAutomizerUnsatResult) res;
					mMostSignificatResults.add(res);
				} else if (res instanceof TimeoutResult) {
					timeoutResult = (TimeoutResult) res;
					mMostSignificatResults.add(res);
				}
			}
		}
		
		if (satResult != null) {
			mOverallResult = TreeAutomizerOverallResult.SAT;
		} else if (unsatResult != null) {
			mOverallResult = TreeAutomizerOverallResult.UNSAT;
		} else if (timeoutResult != null) {
			mOverallResult = TreeAutomizerOverallResult.TIMEOUT;
		} else {
			mOverallResult = TreeAutomizerOverallResult.UNKNOWN;
		}
	}

	@Override
	public TreeAutomizerOverallResult getOverallResult() {
		assert mOverallResult != null;
		return mOverallResult;
	}

	@Override
	public String generateOverallResultMessage() {
		return "most significant results: " + mMostSignificatResults;
	}

	@Override
	public Set<IResult> getMostSignificantResults() {
		return mMostSignificatResults;
	}

}
