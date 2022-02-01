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

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingValueContainer;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * The default rating, simply counts the number of statements which are inside a
 * specific minimized edge.
 * 
 * @author Stefan Wissert
 * 
 */
public class DefaultRating implements IRating {

	private RatingValueContainer<Integer> mCountOfStatements;

	/**
	 * Constructor, which is only visible in this package (default visibility)
	 * 
	 * @param edge
	 *            the edge to be rated
	 */
	DefaultRating(IMinimizedEdge edge) {
		// Basic-Edges have exactly one statement
		if (edge instanceof IBasicEdge) {
			mCountOfStatements = new RatingValueContainer<Integer>(1);
		}
		// For Composite-Edges we summarize the count of statements of the left
		// and the right side
		if (edge instanceof ICompositeEdge) {
			mCountOfStatements = new RatingValueContainer<Integer>(0);
			final ICompositeEdge compEdge = (ICompositeEdge) edge;
			final IMinimizedEdge left = compEdge.getCompositeEdges()[0];
			final IMinimizedEdge right = compEdge.getCompositeEdges()[1];
			if (!(left.getRating() instanceof DefaultRating)
					|| !(right.getRating() instanceof DefaultRating)) {
				throw new IllegalArgumentException(
						"Rating-Objects should be of the same type!");
			}
			final DefaultRating leftRating = (DefaultRating) left.getRating();
			final DefaultRating rightRating = (DefaultRating) right.getRating();
			mCountOfStatements.setValue(leftRating.getRatingValueContainer()
					.getValue()
					+ rightRating.getRatingValueContainer().getValue());
		}
	}

	/**
	 * Constructor to create a rating for a heuristic, should be used only for
	 * this operation. To protect it from misuse the visibility is default.
	 * 
	 * @param value
	 *            the preference value
	 */
	public DefaultRating(String prefValue) {
		// Here we interpret the preference string
		mCountOfStatements = new RatingValueContainer<Integer>(
				Integer.parseInt(prefValue));
	}

	@Override
	public RatingValueContainer<Integer> getRatingValueContainer() {
		return mCountOfStatements;
	}

	@Override
	public int compareTo(IRating other) {
		if (!(other instanceof DefaultRating)) {
			throw new IllegalArgumentException(
					"Comparison of different Ratings is forbidden!");
		}
		final DefaultRating otherRating = (DefaultRating) other;
		return mCountOfStatements.getValue().compareTo(
				otherRating.getRatingValueContainer().getValue());
	}

	@Override
	public int getRatingValueAsInteger() {
		return mCountOfStatements.getValue();
	}

}
