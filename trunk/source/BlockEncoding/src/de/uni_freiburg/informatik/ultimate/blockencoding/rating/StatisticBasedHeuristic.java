/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * To determine a good boundary, which is later used to estimate a good edge
 * level, we use here statistic values of the minimized program. These
 * statistical values are determined during the minimization process.
 * 
 * @author Stefan Wissert
 * 
 */
public class StatisticBasedHeuristic extends ConfigurableHeuristic {

	/**
	 * TODO: Strategies for which we can use these statistics, should be entered
	 * in this list!
	 */
	private final ArrayList<RatingStrategy> mSupportedStrategies;
	private final ILogger mLogger;

	/**
	 * @param strategy
	 */
	public StatisticBasedHeuristic(final RatingStrategy strategy, final ILogger logger) {
		super(strategy);
		mLogger = logger;
		mSupportedStrategies = new ArrayList<RatingStrategy>();
		mSupportedStrategies.add(RatingStrategy.DISJUNCTIVE_STMTCOUNT);
		mSupportedStrategies.add(RatingStrategy.USED_VARIABLES_RATING);
		mSupportedStrategies.add(RatingStrategy.DISJUNCTIVE_VARIABLES_RATING);
	}

	@Override
	public void init(String givenPref) {
		switch (mStrategy) {
		case DISJUNCTIVE_STMTCOUNT:
			givenPref = computeDisStmtBoundary();
			break;
		case USED_VARIABLES_RATING:
			givenPref = computeUsedVarBoundary();
			break;
		case DISJUNCTIVE_VARIABLES_RATING:
			givenPref = computeMultiplicativeBoundary(givenPref);
			break;
		default:
			throw new IllegalArgumentException(
					"Statistic Based Heuristic is not supported for this kind of rating");
		}
		super.init(givenPref);
	}

	@Override
	public boolean isRatingStrategySupported(final RatingStrategy strategy) {
		return mSupportedStrategies.contains(strategy);
	}

	/**
	 * @return
	 */
	private String computeDisStmtBoundary() {
		final StringBuilder sb = new StringBuilder();
		// TODO: validate that
		// we take half of the maximum disjunctions in the graph
		final int disjunctions = 2 * (EncodingStatistics.maxDisjunctionsInOneEdge / 3);
		sb.append(disjunctions);
		sb.append("-");
		// as a upper bound we take 80% of the value
		// maxElementesInOneDisjunction
		final double onePercent = EncodingStatistics.maxElementsInOneDisjunction / 100;
		sb.append((int) (onePercent * 80));
		sb.append("-");
		// as lower bound we take 10% but at least 5 elements
		if (onePercent * 10 < 5) {
			sb.append(5);
		} else {
			sb.append((int) (onePercent * 10));
		}
		return sb.toString();
	}

	/**
	 * @return
	 */
	private String computeUsedVarBoundary() {
		// Basically we take here the arithmetic mean of min and max
		final int meanValue = (int) (1.5 * ((EncodingStatistics.minDiffVariablesInOneEdge + EncodingStatistics.maxDiffVariablesInOneEdge) / 2));
		return Integer.toString(meanValue);
	}

	private String computeMultiplicativeBoundary(final String pref) {
		int value;
		if (!pref.equals("")) {
			final int preference = Integer.parseInt(pref);
			final double onePercent = EncodingStatistics.maxRatingInOneEdge / 100.00;
			final double calc = onePercent * preference;
			value = (int) calc;
		} else {
			value = EncodingStatistics.totalRCFGRating / EncodingStatistics.countOfBasicEdges;
		}
		mLogger.warn("BoundValue: " + value);
		return Integer.toString(value);
	}
}
