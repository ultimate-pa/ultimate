/*
 * Copyright (C) 2018 schaetzc@tf.uni-freiburg.de
 * Copyright (C) 2009-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Removes dead transitions in a Petri Net preserving its language.
 * A transition t is dead iff there is no firing sequence containing t and ending in an accepting marking.
 * Dead transitions do not contribute to the accepted language.
 * <p>
 * This operation may also remove places that do not contribute to the accepted language.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public class RemoveDead<LETTER, PLACE, CRSF extends
		IStateFactory<PLACE> & IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private final BoundedPetriNet<LETTER, PLACE> mOperand;
	private BranchingProcess<LETTER, PLACE> mFinPre;
	private final Set<ITransition<LETTER, PLACE>> mVitalTransitions;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	public RemoveDead(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException {
		this(services, operand, null);
	}

	public RemoveDead(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand,
			BranchingProcess<LETTER, PLACE> finPre) throws AutomataOperationCanceledException {
		super(services);
		mLogger.warn("Operation not fully implemented. Some dead transitions won't removed.");
		mOperand = operand;
		mFinPre = finPre;
		mVitalTransitions = vitalTransitions();
		mResult = new CopySubnet<>(services, mOperand, mVitalTransitions).getResult();
	}

	private Set<ITransition<LETTER, PLACE>> vitalTransitions() throws AutomataOperationCanceledException {
		Set<ITransition<LETTER, PLACE>> vitalTransitions = transitivePredecessors(mOperand.getAcceptingPlaces());
		if (vitalTransitions.size() == mOperand.getTransitions().size()) {
			mLogger.debug("Skipping co-relation queries. All transitions lead to accepting places.");
			return vitalTransitions;
		}
		mFinPre = new FinitePrefix<>(mServices, mOperand).getResult();
		final Collection<Condition<LETTER, PLACE>> acceptingConditions = acceptingConditions();
		mFinPre.getEvents().stream()
			// optimization to reduce number of co-relation queries
			.filter(event -> !vitalTransitions.contains(event.getTransition()))
			.filter(event -> !timeout())
			.filter(event -> coRelatedToAny(event, acceptingConditions))
			.map(Event::getTransition).forEach(vitalTransitions::add);

		if (timeout()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}

		return vitalTransitions;
	}

	private boolean timeout() {
		return !mServices.getProgressAwareTimer().continueProcessing();
	}

	private Set<ITransition<LETTER, PLACE>> transitivePredecessors(final Collection<PLACE> places) {
		final Set<ITransition<LETTER, PLACE>> transitivePredecessors = new HashSet<>();
		final Set<PLACE> visited = new HashSet<>();
		final Queue<PLACE> work = new LinkedList<>(places);
		while (!work.isEmpty()) {
			final PLACE place = work.poll();
			for (final ITransition<LETTER, PLACE> predTransition : mOperand.getPredecessors(place)) {
				transitivePredecessors.add(predTransition);
				mOperand.getPredecessors(predTransition).stream()
					.filter(visited::add).forEach(work::add);
			}
		}
		return transitivePredecessors;
	}

	private boolean coRelatedToAny(Event<LETTER, PLACE> event, Collection<Condition<LETTER, PLACE>> conditions) {
		// TODO implement

		return false;
	}

	private Collection<Condition<LETTER, PLACE>> acceptingConditions() {
		assert mFinPre != null : "Finite prefix not computed yet.";
		return mOperand.getAcceptingPlaces().stream()
				.map(mFinPre::place2cond).flatMap(Collection::stream)
				.collect(Collectors.toList());
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}
		final boolean correct = PetriNetUtils.isEquivalent(mServices, stateFactory, mOperand, mResult);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_PLACES , mOperand.getPlaces().size() - mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_TRANSITIONS, mOperand.getTransitions().size() - mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_FLOW, mOperand.flowSize() - mResult.flowSize());

		statistics.addKeyValuePair(
				StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_PLACES , mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_FLOW, mResult.flowSize());

		return statistics;
	}

}



