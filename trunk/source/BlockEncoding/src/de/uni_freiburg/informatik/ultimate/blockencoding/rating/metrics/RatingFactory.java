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
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;

/**
 * Factory class to create ratings for the edges in the minimized CFG. There
 * will be different strategies how to create such a rating, the only valid way
 * for creation is this class.
 * 
 * @author Stefan Wissert
 * 
 */
public final class RatingFactory {
	/**
	 * This enumeration specifies the RatingStrategy. It can be set in the
	 * preferences. Every new strategy has to be declared here.
	 */
	public static enum RatingStrategy {
		/**
		 * use large block encoding, there is no special rating
		 */
		LARGE_BLOCK,
		/**
		 * The default strategy, is to count the statements.
		 */
		DEFAULT,
		/**
		 * This strategy counts the amount of disjunctions.
		 */
		DISJUNCTIVE_RATING,
		/**
		 * Here we count the disjunctive in context of the amount of statements
		 * which is inherited inside the disjunctions.
		 */
		DISJUNCTIVE_STMTCOUNT,
		/**
		 * Here we count the number of used variables in one edge, this maybe a
		 * good value to measure the complexity of one edge.
		 */
		USED_VARIABLES_RATING,
		/**
		 * Here we count the disjunctions and multiply the results with the
		 * number of used variables.
		 */
		DISJUNCTIVE_VARIABLES_RATING,
		/**
		 * Here we count the disjunctions and multiply the results with the
		 * amount of statements.
		 */
		DISJUNCTIVE_MULTI_STATEMENT_RATING
	}

	/**
	 * there is only one instance of this factory
	 */
	private static RatingFactory instance;

	/**
	 * 
	 */
	private RatingStrategy strategy;

	/**
	 * We do not allow to create instances of this class.
	 */
	private RatingFactory() {
		strategy = RatingFactory.RatingStrategy.DEFAULT;
	}

	/**
	 * Returns the instance of this factory.
	 * 
	 * @return the only existing instance of RatingFactory
	 */
	public static RatingFactory getInstance() {
		if (instance == null) {
			instance = new RatingFactory();
		}
		return instance;
	}

	/**
	 * Setting up the strategy for rating of the edges.
	 * 
	 * @param value
	 *            the preference value
	 */
	public void setRatingStrategy(final String value) {
		try {
			strategy = RatingStrategy.values()[Integer.parseInt(value)];
		} catch (final NumberFormatException e) {
			throw new IllegalArgumentException(
					"There is something wrong, with the enum setup");
		}
	}
	
	public void setRatingStrategy(final RatingStrategy strat){
		strategy = strat;
	}

	/**
	 * Creates a rating for a given minimized edge. In order to do this, there
	 * are different strategies (which can be set, via the preferences).
	 * 
	 * @param edge
	 *            the minimized edge, which we want to rate
	 * @return the created rating for the minimized edge
	 */
	public IRating createRating(final IMinimizedEdge edge) {
		IRating computedRating = null;
		switch (strategy) {
		case LARGE_BLOCK:
		case DEFAULT:
			computedRating = new DefaultRating(edge);
			break;
		case DISJUNCTIVE_RATING:
			computedRating = new DisjunctiveRating(edge);
			break;
		case DISJUNCTIVE_STMTCOUNT:
			computedRating = new DisjunctiveStatementsRating(edge);
			break;
		case USED_VARIABLES_RATING:
			computedRating = new UsedVariablesRating(edge);
			break;
		case DISJUNCTIVE_VARIABLES_RATING:
			computedRating = new DisjunctVariablesRating(edge);
			break;
		case DISJUNCTIVE_MULTI_STATEMENT_RATING:
			computedRating = new DisjunctMultiStatementRating(edge);
			break;
		default:
			throw new IllegalArgumentException("No valid strategy choosen!");
		}
		EncodingStatistics.setMaxRatingOneEdge(
				computedRating.getRatingValueAsInteger(), edge);
		return computedRating;
	}
}
