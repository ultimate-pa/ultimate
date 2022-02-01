/*
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.MSODResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * @author hauffn@informatik.uni-freiburg.de
 * @author henkele@informatik.uni-freiburg.de
 */
public class MSODOverallResultEvaluator implements IOverallResultEvaluator<LBool> {
	private LBool mOverallResult;

	@Override
	public void evaluateOverallResult(final IResultService resultService) {
		for (final Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			for (final IResult result : entry.getValue()) {

				if (result instanceof MSODResult) {
					assert (mOverallResult == null);
					mOverallResult = ((MSODResult) result).getValue();
				}
			}
		}
	}

	@Override
	public LBool getOverallResult() {
		return mOverallResult;
	}

	@Override
	public String generateOverallResultMessage() {
		return "MSOD resulted in: " + mOverallResult.toString();
	}

	@Override
	public Set<IResult> getMostSignificantResults() {
		return Collections.emptySet();
	}
}
