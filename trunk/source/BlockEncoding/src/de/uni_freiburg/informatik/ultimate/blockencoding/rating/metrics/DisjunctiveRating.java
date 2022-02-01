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

import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Here we rate an CodeBlock: <br>
 * - BasicEdges := 0; <br>
 * - Conjunction := 0 <br>
 * - Disjunction := 1 <br>
 * So the rated value is the count of the disjunctions inside this formula.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctiveRating implements IRating {

	private RatingValueContainer<Integer> countOfDisjunctions;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            the edge to be rated
	 */
	DisjunctiveRating(IMinimizedEdge edge) {
		if (edge.isBasicEdge()) {
			countOfDisjunctions = new RatingValueContainer<Integer>(0);
		}

		// We only care for composite edges, since basic edge do not contain
		// disjunctions, so there rating = 0
		if (edge instanceof ICompositeEdge) {
			final ICompositeEdge compEdge = (ICompositeEdge) edge;
			final IMinimizedEdge left = compEdge.getCompositeEdges()[0];
			final IMinimizedEdge right = compEdge.getCompositeEdges()[1];
			if (!(left.getRating() instanceof DisjunctiveRating)
					|| !(right.getRating() instanceof DisjunctiveRating)) {
				throw new IllegalArgumentException(
						"Rating-Objects should be of the same type!");
			}
			final DisjunctiveRating leftRating = (DisjunctiveRating) left.getRating();
			final DisjunctiveRating rightRating = (DisjunctiveRating) right
					.getRating();
			// Since the underlying edge is a composite, we have to examine the
			// left and the right side of the Disjunction
			countOfDisjunctions = new RatingValueContainer<Integer>(leftRating
					.getRatingValueContainer().getValue()
					+ rightRating.getRatingValueContainer().getValue());
			// if this edge itself is a Disjunction we have to add this
			if (edge instanceof DisjunctionEdge) {
				countOfDisjunctions
						.setValue(countOfDisjunctions.getValue() + 1);
			}
		}
	}

	/**
	 * Constructor to create a rating boundary for the heuristic, visibility is
	 * default (package)
	 * 
	 * @param value
	 *            the preference value
	 */
	public DisjunctiveRating(String prefValue) {
		countOfDisjunctions = new RatingValueContainer<Integer>(
				Integer.parseInt(prefValue));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof DisjunctiveRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		return countOfDisjunctions.getValue().compareTo(
				((DisjunctiveRating) other).getRatingValueContainer()
						.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating
	 * #getRatingValue()
	 */
	@Override
	public RatingValueContainer<Integer> getRatingValueContainer() {
		return countOfDisjunctions;
	}

	@Override
	public int getRatingValueAsInteger() {
		return countOfDisjunctions.getValue();
	}

}
