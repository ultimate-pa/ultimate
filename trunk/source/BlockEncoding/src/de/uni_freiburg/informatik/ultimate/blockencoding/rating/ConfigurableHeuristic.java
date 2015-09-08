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
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.UsedVariablesRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;

/**
 * Basically this "heuristic" takes the values, which are specified on the
 * preference page.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConfigurableHeuristic implements IRatingHeuristic {

	protected RatingStrategy strategy;

	protected IRating boundary;

	/**
	 * Public constructor needs the used strategy to interpret the given values.
	 * 
	 * @param strategy
	 *            the used RatingStrategy
	 */
	public ConfigurableHeuristic(RatingStrategy strategy) {
		this.strategy = strategy;
	}

	@Override
	public void init(String givenPref) {
		// Determine the used strategy
		switch (strategy) {
		case LARGE_BLOCK:
			throw new IllegalArgumentException(
					"For Large Block Encoding, there is no heuristic needed");
		case DEFAULT:
			boundary = new DefaultRating(givenPref);
			break;
		case DISJUNCTIVE_RATING:
			boundary = new DisjunctiveRating(givenPref);
			break;
		case DISJUNCTIVE_STMTCOUNT:
			boundary = new DisjunctiveStatementsRating(givenPref);
			break;
		case USED_VARIABLES_RATING:
			boundary = new UsedVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_VARIABLES_RATING:
			boundary = new DisjunctVariablesRating(givenPref);
			break;
		case DISJUNCTIVE_MULTI_STATEMENT_RATING:
			boundary = new DisjunctMultiStatementRating(givenPref);
			break;
		default:
			throw new IllegalArgumentException(
					"Unkown state of the enum RatingStrategy,"
							+ " need to place all possibilites here!");
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.
	 * IRatingHeuristic
	 * #isRatingBoundReached(de.uni_freiburg.informatik.ultimate.
	 * blockencoding.rating.interfaces.IRating)
	 */
	@Override
	public boolean isRatingBoundReached(IRating rating, List<IMinimizedEdge> edgeLevel) {
		if (boundary == null) {
			throw new IllegalArgumentException("No boundary rating specified");
		}
		return rating.compareTo(boundary) <= 0;
	}

	@Override
	public boolean isRatingStrategySupported(RatingStrategy strategy) {
		// here every strategy should be supported!
		return true;
	}

}
