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
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DefaultRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctMultiStatementRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctVariablesRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctiveRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctiveStatementsRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.UsedVariablesRating;

/**
 * Basically this "heuristic" takes the values, which are specified on the
 * preference page.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConfigurableHeuristic implements IRatingHeuristic {

	protected RatingStrategy mStrategy;

	protected IRating mBoundary;

	/**
	 * Public constructor needs the used strategy to interpret the given values.
	 * 
	 * @param strategy
	 *            the used RatingStrategy
	 */
	public ConfigurableHeuristic(RatingStrategy strategy) {
		mStrategy = strategy;
	}

	@Override
	public void init(String givenPref) {
		// Determine the used strategy
		switch (mStrategy) {
		case LARGE_BLOCK:
			throw new IllegalArgumentException(
					"For Large Block Encoding, there is no heuristic needed");
		case DEFAULT:
			mBoundary = new DefaultRating(givenPref);
			break;
		case DISJUNCTIVE_RATING:
			mBoundary = new DisjunctiveRating(givenPref);
			break;
		case DISJUNCTIVE_STMTCOUNT:
			mBoundary = new DisjunctiveStatementsRating(givenPref);
			break;
		case USED_VARIABLES_RATING:
			mBoundary = new UsedVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_VARIABLES_RATING:
			mBoundary = new DisjunctVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_MULTI_STATEMENT_RATING:
			mBoundary = new DisjunctMultiStatementRating(givenPref);
			break;
		default:
			throw new IllegalArgumentException(
					"Unkown state of the enum RatingStrategy,"
							+ " need to place all possibilites here!");
		}
	}

	@Override
	public boolean isRatingBoundReached(IRating rating, List<IMinimizedEdge> edgeLevel) {
		if (mBoundary == null) {
			throw new IllegalArgumentException("No boundary rating specified");
		}
		return rating.compareTo(mBoundary) <= 0;
	}

	@Override
	public boolean isRatingStrategySupported(RatingStrategy strategy) {
		return true;
	}

}
