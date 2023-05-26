/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Petri net unfolder.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <L>
 *            symbol type
 * @param <P>
 *            place content type
 */
public final class PetriNetUnfolder<L, P> extends PetriNetUnfolderBase<L, P, PetriNetRun<L, P>> {
	/**
	 * Build the finite Prefix of PetriNet net.
	 *
	 * @param order
	 *            the order on events and configurations respectively is used to determine cut-off events.
	 * @param sameTransitionCutOff
	 *            if true, an additional condition for cut-off events is used: An event and its companion must belong to
	 *            the same transition from the net.
	 * @param stopIfAcceptingRunFound
	 *            if false, the complete finite Prefix will be build.
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 * @throws PetriNetNot1SafeException
	 */
	public PetriNetUnfolder(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<L, P> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	public enum EventOrderEnum {
		DBO("Depth-based Order"), ERV("Esparza Römer Vogler"), KMM("Ken McMillan"),;

		private String mDescription;

		EventOrderEnum(final String name) {
			mDescription = name;
		}

		public String getDescription() {
			return mDescription;
		}
	}

	@Override
	protected boolean checkInitialPlaces() {
		return mUnfolding.getDummyRoot().getSuccessorConditions().stream()
				.anyMatch(c -> mOperand.isAccepting(c.getPlace()));
	}

	@Override
	protected PetriNetRun<L, P> constructInitialRun() throws PetriNetNot1SafeException {
		return new PetriNetRun<>(
				new ConditionMarking<>(mUnfolding.getDummyRoot().getSuccessorConditions()).getMarking());
	}

	@Override
	protected boolean addAndCheck(final Event<L, P> event) throws PetriNetNot1SafeException {
		return mUnfolding.addEvent(event);
	}

	@Override
	protected PetriNetRun<L, P> constructRun(final Event<L, P> event) {
		/**
		 * constructs a run over the unfolding which leads to the marking corresponding with the local configuration of
		 * the specified event e.
		 * <p>
		 * uses the recursive helper-method {@code #constructRun(Event, Marking)}
		 */
		mLogger.debug("Marking: " + mUnfolding.getDummyRoot().getMark());
		try {
			return constructRun(event, mUnfolding.getDummyRoot().getConditionMark()).mRunInner;
		} catch (final PetriNetNot1SafeException e) {
			throw new AssertionError("Petri net not one safe for places " + e.getUnsafePlaces()
					+ " but this should have been detected earlier.");
		}
	}

	class RunAndConditionMarking {
		private final PetriNetRun<L, P> mRunInner;
		private final ConditionMarking<L, P> mMarking;

		public RunAndConditionMarking(final PetriNetRun<L, P> run, final ConditionMarking<L, P> marking) {
			mRunInner = run;
			mMarking = marking;
		}
	}

	/**
	 * Recursively builds a part of a run over the unfolding which leads to the marking corresponding with the local
	 * configuration of the specified event e.
	 * <p>
	 * The run starts with the given Marking {@code initialMarking}
	 */
	private RunAndConditionMarking constructRun(final Event<L, P> event, final ConditionMarking<L, P> initialMarking)
			throws PetriNetNot1SafeException {
		assert event != mUnfolding.getDummyRoot();
		assert !event.getPredecessorConditions().isEmpty();
		if (EXTENDED_ASSERTION_CHECKING) {
			assert !mUnfolding.pairwiseConflictOrCausalRelation(event.getPredecessorConditions());
		}
		PetriNetRun<L, P> run = new PetriNetRun<>(initialMarking.getMarking());
		ConditionMarking<L, P> current = initialMarking;
		for (final Condition<L, P> c : event.getPredecessorConditions()) {
			if (current.contains(c)) {
				continue;
			}
			final RunAndConditionMarking result = constructRun(c.getPredecessorEvent(), current);
			run = run.concatenate(result.mRunInner);
			current = result.mMarking;
		}
		assert current != null;

		final ConditionMarking<L, P> finalMarking = current.fireEvent(event);
		final Transition<L, P> t = event.getTransition();
		final PetriNetRun<L, P> appendix = new PetriNetRun<>(current.getMarking(), t, finalMarking.getMarking());
		run = run.concatenate(appendix);

		mLogger.debug("Event  : " + event);
		mLogger.debug("Marking: " + run.getMarking(run.getWord().length()));
		return new RunAndConditionMarking(run, finalMarking);
	}

	@Override
	protected boolean checkRun(final IPetriNet2FiniteAutomatonStateFactory<P> stateFactory, final PetriNetRun<L, P> run)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger.info("Testing correctness of emptinessCheck");
		if (!(mOperand instanceof IPetriNetTransitionProvider)) {
			mLogger.warn("Will not check Unfolding because operand is constructed on-demand");
			return true;
		}

		boolean correct;
		if (run == null) {
			final NestedRun<L, P> automataRun = (new IsEmpty<>(mServices, (new PetriNet2FiniteAutomaton<>(mServices,
					stateFactory, (IPetriNetTransitionProvider<L, P>) mOperand)).getResult())).getNestedRun();
			if (automataRun != null) {
				// TODO Christian 2016-09-30: This assignment is useless - a bug?
				correct = false;
				mLogger.error("EmptinessCheck says empty, but net accepts: " + automataRun.getWord());
			}
			correct = automataRun == null;
		} else {
			final Word<L> word = run.getWord();
			if (new Accepts<>(mServices, (IPetriNetTransitionProvider<L, P>) mOperand, word).getResult()) {
				correct = true;
			} else {
				mLogger.error("Result of EmptinessCheck, but not accepted: " + word);
				correct = false;
			}
		}
		mLogger.info("Finished testing correctness of emptinessCheck");
		return correct;
	}
}
