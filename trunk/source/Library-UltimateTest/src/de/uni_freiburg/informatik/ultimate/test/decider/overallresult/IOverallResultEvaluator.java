/*
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;

/**
 * Classes that implement this interface can be used to evaluate an overall result.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT>
 *            Type that we use to represent possible overall results. Typically we use an enum type.
 */
public interface IOverallResultEvaluator<OVERALL_RESULT> {

	/**
	 * Use the IResults computed by Ultimate to evaluate an overall result. This method should compute the overall
	 * result and the most significant IResults such that both will be available using the getters below.
	 */
	public void evaluateOverallResult(IResultService resultService);

	/**
	 * Getter for overall result. Should be called only after the overall result was computed by the
	 * evaluateOverallResult(...) method.
	 */
	public OVERALL_RESULT getOverallResult();

	/**
	 * Returns a String that describes the overall result. This can be getOverallResult().toString(), but desirable is a
	 * more detailed description.
	 *
	 */
	public String generateOverallResultMessage();

	/**
	 * Returns all IResults that are most significant while evaluating the overall result. E.g., if a safety checker
	 * reports some UNKNOWN IResults and some UNSAFE IResults, the UNSAFE IResults are more significant because they
	 * determine that the overall result is UNSAFE
	 */
	public Set<IResult> getMostSignificantResults();

}
