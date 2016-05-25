/*
 * Copyright (C) 2012-2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;

/**
 * This edge represents a disjunction of the formulas of two edges. This is here only virtually, that means we keep here
 * only the references. The "real" disjunction (parallel composition) is done later, when we generate the new minimized
 * graph.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctionEdge extends AbstractCompositeEdge {

	/**
	 * Serial number, do not really use it.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the rating for this Disjunction-Edge
	 */
	private IRating mRating;

	/**
	 * @param left
	 * @param right
	 */
	public DisjunctionEdge(IMinimizedEdge left, IMinimizedEdge right) {
		super(left, right);
		mContainedDisjunctions++;
		mRating = RatingFactory.getInstance().createRating(this);
		EncodingStatistics.incCountOfDisjunctions();
		EncodingStatistics.setMaxDisjunctionsInOneEdge(mContainedDisjunctions);
		EncodingStatistics.setMaxElementsInOneDisjunction(getElementCount());
	}

	/**
	 * Empty constructor, is needed to create edges for rating boundary
	 */
	public DisjunctionEdge() {

	}

	@Override
	public IRating getRating() {
		return mRating;
	}
}
