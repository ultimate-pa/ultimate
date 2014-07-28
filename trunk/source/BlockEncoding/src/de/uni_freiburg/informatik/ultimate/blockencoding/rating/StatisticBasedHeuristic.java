/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;

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
	private ArrayList<RatingStrategy> mSupportedStrategies;
	private Logger mLogger;

	/**
	 * @param strategy
	 */
	public StatisticBasedHeuristic(RatingStrategy strategy, Logger logger) {
		super(strategy);
		mLogger = logger;
		mSupportedStrategies = new ArrayList<RatingStrategy>();
		mSupportedStrategies.add(RatingStrategy.DISJUNCTIVE_STMTCOUNT);
		mSupportedStrategies.add(RatingStrategy.USED_VARIABLES_RATING);
		mSupportedStrategies.add(RatingStrategy.DISJUNCTIVE_VARIABLES_RATING);
	}

	@Override
	public void init(String givenPref) {
		switch (this.strategy) {
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
	public boolean isRatingStrategySupported(RatingStrategy strategy) {
		return mSupportedStrategies.contains(strategy);
	}

	/**
	 * @return
	 */
	private String computeDisStmtBoundary() {
		StringBuilder sb = new StringBuilder();
		// TODO: validate that
		// we take half of the maximum disjunctions in the graph
		int disjunctions = (int) (2 * (EncodingStatistics.maxDisjunctionsInOneEdge / 3));
		sb.append(disjunctions);
		sb.append("-");
		// as a upper bound we take 80% of the value
		// maxElementesInOneDisjunction
		double onePercent = EncodingStatistics.maxElementsInOneDisjunction / 100;
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
		int meanValue = (int) (1.5 * ((EncodingStatistics.minDiffVariablesInOneEdge + EncodingStatistics.maxDiffVariablesInOneEdge) / 2));
		return Integer.toString(meanValue);
	}

	private String computeMultiplicativeBoundary(String pref) {
		int value;
		if (!pref.equals("")) {
			int preference = Integer.parseInt(pref);
			double onePercent = (double)EncodingStatistics.maxRatingInOneEdge / 100.00;
			double calc = onePercent * (double)preference;
			value = (int) calc;
		} else {
			value = EncodingStatistics.totalRCFGRating / EncodingStatistics.countOfBasicEdges;
		}
		mLogger.warn("BoundValue: " + value);
		return new Integer(value).toString();
	}
}
