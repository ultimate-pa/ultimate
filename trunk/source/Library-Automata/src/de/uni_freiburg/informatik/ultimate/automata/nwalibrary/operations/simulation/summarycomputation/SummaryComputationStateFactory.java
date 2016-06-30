/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.summarycomputation;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

public class SummaryComputationStateFactory extends StateFactory<ISummaryComputationWrapperState> {
	
	private static final ISummaryComputationWrapperState EMPTY_STACK_STATE = new ISummaryComputationWrapperState() {

		@Override
		public String toString() {
			return "I am the auxiliary emtpy stack state";
		}
		
	};

	@Override
	public ISummaryComputationWrapperState intersection(ISummaryComputationWrapperState s1,
			ISummaryComputationWrapperState s2) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState intersectBuchi(ISummaryComputationWrapperState s1,
			ISummaryComputationWrapperState s2, int track) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState determinize(
			Map<ISummaryComputationWrapperState, Set<ISummaryComputationWrapperState>> down2up) {
		return new SummaryComputationDoubleDeckerSet(down2up);
	}

	@Override
	public ISummaryComputationWrapperState createSinkStateContent() {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState createEmptyStackState() {
		return EMPTY_STACK_STATE;
	}

	@Override
	public ISummaryComputationWrapperState getContentOnPetriNet2FiniteAutomaton(
			Marking<?, ISummaryComputationWrapperState> marking) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState getContentOnConcurrentProduct(ISummaryComputationWrapperState c1,
			ISummaryComputationWrapperState c2) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState getWhiteContent(ISummaryComputationWrapperState c) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState getBlackContent(ISummaryComputationWrapperState c) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState buchiComplementFKV(
			LevelRankingState<?, ISummaryComputationWrapperState> compl) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState buchiComplementNCSB(
			LevelRankingState<?, ISummaryComputationWrapperState> compl) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState complementBuchiDeterministicNonFinal(ISummaryComputationWrapperState c) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState complementBuchiDeterministicFinal(ISummaryComputationWrapperState c) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState minimize(Collection<ISummaryComputationWrapperState> states) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState createDoubleDeckerContent(ISummaryComputationWrapperState down,
			ISummaryComputationWrapperState up) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState constructBuchiSVWState(Integer stateNb, Integer tmaNb) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState finitePrefix2net(Condition<?, ISummaryComputationWrapperState> c) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}

	@Override
	public ISummaryComputationWrapperState senwa(ISummaryComputationWrapperState entry,
			ISummaryComputationWrapperState state) {
		throw new UnsupportedOperationException("operation not needed for summary computation");
	}


}
