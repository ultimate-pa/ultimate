/*
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

/**
 * Collects statistics about a {@link LiptonReduction}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class LiptonReductionStatisticsGenerator extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	private int mPlacesBefore = -1;
	private int mTransitionsBefore = -1;
	private int mCoEnabledTransitionPairs = -1;
	private int mPlacesAfterwards = -1;
	private int mTransitionsAfterwards = -1;

	private int mNumberOfFixpointIterations;

	private int mTrivialSequentialCompositions;
	private int mConcurrentSequentialCompositions;
	private int mTrivialYvCompositions;
	private int mConcurrentYvCompositions;
	private int mChoiceCompositions;
	private int mTotalNumberOfCompositions;

	public void reportFixpointIteration() {
		mNumberOfFixpointIterations++;
	}

	public void reportComposition(final LiptonReductionStatisticsDefinitions type) {
		switch (type) {
		case TrivialSequentialCompositions:
			mTrivialSequentialCompositions++;
			break;
		case ConcurrentSequentialCompositions:
			mConcurrentSequentialCompositions++;
			break;
		case TrivialYvCompositions:
			mTrivialYvCompositions++;
			break;
		case ConcurrentYvCompositions:
			mConcurrentYvCompositions++;
			break;
		case ChoiceCompositions:
			mChoiceCompositions++;
			break;
		default:
			throw new UnsupportedOperationException("not an enum for a composition " + type);
		}
		mTotalNumberOfCompositions++;
	}

	public void collectInitialStatistics(final IPetriNet<?, ?> net) {
		mPlacesBefore = net.getPlaces().size();
		mTransitionsBefore = net.getTransitions().size();
	}

	public void collectFinalStatistics(final IPetriNet<?, ?> net) {
		mPlacesAfterwards = net.getPlaces().size();
		mTransitionsAfterwards = net.getTransitions().size();
	}

	public void setCoEnabledTransitionPairs(final int coEnabledTransitionPairs) {
		mCoEnabledTransitionPairs = coEnabledTransitionPairs;
	}

	@Override
	public Collection<String> getKeys() {
		return LiptonReductionStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final LiptonReductionStatisticsDefinitions keyEnum = LiptonReductionStatisticsDefinitions.valueOf(key);
		return getValue(keyEnum);
	}

	public Object getValue(final LiptonReductionStatisticsDefinitions key) {
		switch (key) {
		case ChoiceCompositions:
			return mChoiceCompositions;
		case CoEnabledTransitionPairs:
			return mCoEnabledTransitionPairs;
		case ConcurrentSequentialCompositions:
			return mConcurrentSequentialCompositions;
		case ConcurrentYvCompositions:
			return mConcurrentYvCompositions;
		case FixpointIterations:
			return mNumberOfFixpointIterations;
		case PlacesAfterwards:
			return mPlacesAfterwards;
		case PlacesBefore:
			return mPlacesBefore;
		case ReductionTime:
			try {
				return getElapsedTime(key.toString());
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case TotalNumberOfCompositions:
			return mTotalNumberOfCompositions;
		case TransitionsAfterwards:
			return mTransitionsAfterwards;
		case TransitionsBefore:
			return mTransitionsBefore;
		case TrivialSequentialCompositions:
			return mTrivialSequentialCompositions;
		case TrivialYvCompositions:
			return mTrivialYvCompositions;
		default:
			throw new AssertionError("unknown data: " + key);
		}
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return LiptonReductionStatisticsType.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		return new String[] { LiptonReductionStatisticsDefinitions.ReductionTime.toString() };
	}
}
