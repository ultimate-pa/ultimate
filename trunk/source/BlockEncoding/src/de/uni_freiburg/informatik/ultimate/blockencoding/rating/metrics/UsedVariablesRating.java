/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * In this rating we count the number of used variables, this may be an
 * interesting value to measure the complexity of single formulas.
 * 
 * @author Stefan Wissert
 * 
 */
public class UsedVariablesRating implements IRating {

	private final RatingValueContainer<Integer> countUsedVariables;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            , the edge to be rated
	 */
	UsedVariablesRating(IMinimizedEdge edge) {
		countUsedVariables = new RatingValueContainer<Integer>(edge
				.getDifferentVariables().size());
	}

	/**
	 * Constructor to create a rating boundary for the heuristic, visibility is
	 * default (package)
	 * 
	 * @param value
	 *            the preference value
	 */
	public UsedVariablesRating(String prefValue) {
		countUsedVariables = new RatingValueContainer<Integer>(
				Integer.parseInt(prefValue));
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof UsedVariablesRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		return countUsedVariables.getValue().compareTo(
				((UsedVariablesRating) other).getRatingValueContainer()
						.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating
	 * #getRatingValueContainer()
	 */
	@Override
	public RatingValueContainer<Integer> getRatingValueContainer() {
		return countUsedVariables;
	}

	@Override
	public int getRatingValueAsInteger() {
		return countUsedVariables.getValue();
	}

}
