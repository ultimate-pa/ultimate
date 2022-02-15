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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Collects statistics about a {@link LiptonReduction}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class LiptonReductionStatisticsGenerator extends BaseStatisticsDataProvider {

	public enum LiptonReductionCompositions {
		TrivialSequentialCompositions, ConcurrentSequentialCompositions, TrivialYvCompositions,
		ConcurrentYvCompositions, ChoiceCompositions
	}

	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mReductionTime = new TimeTracker();

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mPlacesBefore = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mTransitionsBefore = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mCoEnabledTransitionPairs = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mPlacesAfterwards = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mTransitionsAfterwards = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mMoverChecksTotal;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER_ZERO)
	private int mNumberOfFixpointIterations = -1;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTrivialSequentialCompositions;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConcurrentSequentialCompositions;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTrivialYvCompositions;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mConcurrentYvCompositions;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mChoiceCompositions;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mTotalNumberOfCompositions;

	public LiptonReductionStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
	}

	public void reportFixpointIteration() {
		mNumberOfFixpointIterations++;
	}

	public void reportMoverChecks(final int numberOfChecks) {
		mMoverChecksTotal += numberOfChecks;
	}

	public void reportComposition(final LiptonReductionCompositions type) {
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

	public void startReductionTime() {
		mReductionTime.start();
	}

	public void stopReductionTime() {
		mReductionTime.stop();
	}

	public int getMoverChecksTotal() {
		return mMoverChecksTotal;
	}

	public int getTotalNumberOfCompositions() {
		return mTotalNumberOfCompositions;
	}

}
