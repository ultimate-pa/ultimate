/*
 * Copyright (C) 2018 schaetzc@tf.uni-freiburg.de
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2009-2023 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Removes dead transitions in a Buchi Petri Net preserving its language. Uses an outdated (possibly removed) algorithm
 * of {@link RemoveDead}. While this does not remove all dead Transitions, the new algorithm of {@link RemoveDead} might
 * remove vital Transitions in the infinite Petri net.
 */
public class RemoveDeadBuchi<LETTER, PLACE, CRSF extends IStateFactory<PLACE> & IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	private BranchingProcess<LETTER, PLACE> mFinPre;
	private Collection<Condition<LETTER, PLACE>> mAcceptingConditions;
	private final Set<Transition<LETTER, PLACE>> mVitalTransitions;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	public RemoveDeadBuchi(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand,
			final BranchingProcess<LETTER, PLACE> finPre)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		if (finPre != null) {
			mFinPre = finPre;
		} else {
			mFinPre = new FinitePrefix<>(services, operand).getResult();
		}
		printStartMessage();
		mVitalTransitions = vitalTransitions();
		mResult = CopySubnet.copy(services, mOperand, mVitalTransitions, mOperand.getAlphabet(), true);
		printExitMessage();
	}

	private Set<Transition<LETTER, PLACE>> vitalTransitions()
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Set<Transition<LETTER, PLACE>> vitalTransitions = transitivePredecessors(mOperand.getAcceptingPlaces());

		if (vitalTransitions.size() == mOperand.getTransitions().size()) {
			mLogger.debug("Skipping co-relation queries. All transitions lead to accepting places.");
		} else {
			ensureFinPreExists();
			mAcceptingConditions = acceptingConditions();
			mFinPre.getEvents().stream().filter(event -> event != mFinPre.getDummyRoot())
					// optimization to reduce number of co-relation queries
					.filter(event -> !vitalTransitions.contains(event.getTransition())).filter(event -> !timeout())
					.filter(this::coRelatedToAnyAccCond).map(Event::getTransition).forEach(vitalTransitions::add);
			if (timeout()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		return vitalTransitions;
	}

	private void ensureFinPreExists() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		if (mFinPre == null) {
			mLogger.info("Computing finite prefix for " + getOperationName());
			mFinPre = new FinitePrefix<>(mServices, mOperand).getResult();
		}
	}

	private boolean timeout() {
		return !mServices.getProgressAwareTimer().continueProcessing();
	}

	private boolean coRelatedToAnyAccCond(final Event<LETTER, PLACE> event) {
		return mAcceptingConditions.stream()
				.anyMatch(condition -> mFinPre.getCoRelation().isInCoRelation(condition, event));
	}

	private Set<Transition<LETTER, PLACE>> transitivePredecessors(final Collection<PLACE> places) {
		final Set<Transition<LETTER, PLACE>> transitivePredecessors = new HashSet<>();
		final Set<PLACE> visited = new HashSet<>();
		final Queue<PLACE> work = new LinkedList<>(places);
		while (!work.isEmpty()) {
			final PLACE place = work.poll();
			for (final Transition<LETTER, PLACE> predTransition : mOperand.getPredecessors(place)) {
				transitivePredecessors.add(predTransition);
				predTransition.getPredecessors().stream().filter(visited::add).forEach(work::add);
			}
		}
		return transitivePredecessors;
	}

	private Collection<Condition<LETTER, PLACE>> acceptingConditions() {
		assert mFinPre != null : "Finite prefix not computed yet.";
		return mOperand.getAcceptingPlaces().stream().map(mFinPre::place2cond).flatMap(Collection::stream)
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
		mLogger.warn("checkResult not implemented-");
		return true;
	}

	@Override
	public String exitMessage() {
		return "Finished " + this.getClass().getSimpleName() + ", result has " + mResult.sizeInformation();
	}
}
