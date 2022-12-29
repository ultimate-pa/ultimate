/*
 * Copyright (C) 2022 Aly Mohsen
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class TraversalStatisticsVisitor<L, S, V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {

	private Statistics mStatistics;
	
	public TraversalStatisticsVisitor(V underlying) {
		super(underlying);
		mStatistics = new Statistics();
		// TODO Auto-generated constructor stub
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}
	
	@Override
	public boolean addStartState(S state) {
		// TODO Auto-generated method stub
		mStatistics.incStates();
		return super.addStartState(state);
	}
	
	@Override
	public boolean discoverState(S state) {
		// TODO Auto-generated method stub
		mStatistics.incStates();
		return super.discoverState(state);
	}
	
	@Override
	public boolean discoverTransition(S source, L letter, S target) {
		// TODO Auto-generated method stub
		mStatistics.incTransitions();
		return super.discoverTransition(source, letter, target);
	}
	
	private final class Statistics extends AbstractStatisticsDataProvider {
		public static final String STATES = "States";
		public static final String TRANSITIONS = "Transitions";

		private int mStates;
		private int mTransitions;

		private Statistics() {
			declare(STATES, () -> mStates, KeyType.COUNTER);
			declare(TRANSITIONS, () -> mTransitions, KeyType.COUNTER);
		}

		private void incStates() {
//			assert mComputationStart == -1 : "Computation timer already running";
			mStates++;
		}
		
		private void incTransitions() {
//			assert mComputationStart == -1 : "Computation timer already running";
			mTransitions++;
		}
		
		 public String toString() {
			 return "States: " + mStates + ", Transitions: " + mTransitions;
		 }
	}
}


