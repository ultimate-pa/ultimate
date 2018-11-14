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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Petri net unfolder.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class PetriNetUnfolder<LETTER, PLACE> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final IPetriNetSuccessorProvider<LETTER, PLACE> mOperand;
	private final boolean mStopIfAcceptingRunFound;
	private final boolean mSameTransitionCutOff;
	private final IOrder<LETTER, PLACE>  mOrder;
	private final IPossibleExtensions<LETTER, PLACE> mPossibleExtensions;
	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	private PetriNetRun<LETTER, PLACE> mRun;

	private final PetriNetUnfolder<LETTER, PLACE>.Statistics mStatistics = new Statistics();


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
	 */
	public PetriNetUnfolder(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, PLACE> operand,
			final UnfoldingOrder order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mStopIfAcceptingRunFound = stopIfAcceptingRunFound;
		mSameTransitionCutOff = sameTransitionCutOff;
		mLogger.debug("Start unfolding. Net " + mOperand.sizeInformation()
				+ (mStopIfAcceptingRunFound ? "We stop if some accepting run was found"
						: "We compute complete finite Prefix"));
		switch (order) {
			case KMM:
				mOrder = new McMillanOrder<>();
				break;
			case ERV_MARK:
				mOrder = new ErvEqualMarkingOrder<>();
				break;
			case ERV:
				mOrder = new EsparzaRoemerVoglerOrder<>();
				break;
			default:
				throw new IllegalArgumentException();
		}
		mUnfolding = new BranchingProcess<>(mServices, operand, mOrder);
		mPossibleExtensions = new PossibleExtensions<>(mUnfolding, mOrder);

		computeUnfolding();
		mLogger.info(mStatistics.cutOffInformation());
		mLogger.info(mStatistics.coRelationInformation());
	}

	public PetriNetUnfolder<LETTER, PLACE>.Statistics getUnfoldingStatistics() {
		return mStatistics;
	}

	private void computeUnfolding() throws AutomataOperationCanceledException {
		boolean someInitialPlaceIsAccepting = false;
		for (final Condition<LETTER, PLACE> c : mUnfolding.getDummyRoot().getSuccessorConditions()) {
			if (mOperand.isAccepting(c.getPlace())) {
				someInitialPlaceIsAccepting = true;
			}
		}
		if (someInitialPlaceIsAccepting) {
			mRun = new PetriNetRun<LETTER, PLACE>(
					new ConditionMarking<>(mUnfolding.getDummyRoot().getSuccessorConditions()).getMarking());
			if (mStopIfAcceptingRunFound) {
				return;
			}
		}
		mPossibleExtensions.update(mUnfolding.getDummyRoot());

		while (!mPossibleExtensions.isEmpy()) {
			final Event<LETTER, PLACE> e = mPossibleExtensions.remove();

			final boolean finished = computeUnfoldingHelper(e);
			if (finished) {
				return;
			}

			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final int numberOfUselessExtensionCandidates = ((PossibleExtensions<LETTER, PLACE>) mPossibleExtensions)
						.getUselessExtensionCandidates();
				final int numberOfExtensionsCandidates = ((PossibleExtensions<LETTER, PLACE>) mPossibleExtensions)
						.getUsefulExtensionCandidates() + numberOfUselessExtensionCandidates;
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
						"constructing finite prefix that currently has " + mUnfolding.getConditions().size()
								+ " conditions, " + mUnfolding.getEvents().size() + " events, and "
								+ mPossibleExtensions.size() + " possible extensions. " + numberOfExtensionsCandidates
								+ " extension candidates were considered " + numberOfUselessExtensionCandidates
								+ " were useless");
				throw new AutomataOperationCanceledException(rti);
			}
		}
	}

	private boolean computeUnfoldingHelper(final Event<LETTER, PLACE> event) {
		assert !parentIsCutoffEvent(event) : "We must not construct successors of cut-off events.";
		final boolean succOfEventIsAccpting = mUnfolding.addEvent(event);
		// assert !unfolding.pairwiseConflictOrCausalRelation(e.getPredecessorConditions());
		if (succOfEventIsAccpting && mRun == null) {
			mRun = constructRun(event);
			if (mStopIfAcceptingRunFound) {
				return true;
			}
		}
		if (mUnfolding.isCutoffEvent(event, mOrder, mSameTransitionCutOff)) {
			mLogger.debug("Constructed     Cut-off-Event: " + event.toString());
		} else {
			final long sizeBefore = mPossibleExtensions.size();
			mPossibleExtensions.update(event);
			final long newPossibleExtensions = mPossibleExtensions.size() - sizeBefore;
			mLogger.debug("Constructed Non-cut-off-Event: " + event.toString());
			mLogger.debug("The Event lead to " + newPossibleExtensions + " new possible extensions.");
		}
		mLogger.debug("Possible Extension size: " + mPossibleExtensions.size() + ", total #Events: "
				+ mUnfolding.getEvents().size() + ", total #Conditions: " + mUnfolding.getConditions().size());
		mStatistics.add(event);
		return false;
	}

	/**
	 * constructs a run over the unfolding which leads to the marking corresponding with the local configuration of the
	 * specified event e.
	 * <p>
	 * uses the recursive helper-method {@code #constructRun(Event, Marking)}
	 */
	private PetriNetRun<LETTER, PLACE> constructRun(final Event<LETTER, PLACE> event) {
		mLogger.debug("Marking: " + mUnfolding.getDummyRoot().getMark());
		return constructRun(event, mUnfolding.getDummyRoot().getConditionMark()).mRunInner;
	}

	/**
	 * Recursively builds a part of a run over the unfolding which leads to the marking corresponding with the local
	 * configuration of the specified event e.
	 * <p>
	 * The run starts with the given Marking {@code initialMarking}
	 */
	private RunAndConditionMarking constructRun(final Event<LETTER, PLACE> event, final ConditionMarking<LETTER, PLACE> initialMarking) {
		assert event != mUnfolding.getDummyRoot();
		assert !event.getPredecessorConditions().isEmpty();
		assert !mUnfolding.pairwiseConflictOrCausalRelation(event.getPredecessorConditions());
		PetriNetRun<LETTER, PLACE> run = new PetriNetRun<>(initialMarking.getMarking());
		ConditionMarking<LETTER, PLACE> current = initialMarking;
		for (final Condition<LETTER, PLACE> c : event.getPredecessorConditions()) {
			if (current.contains(c)) {
				continue;
			}
			final RunAndConditionMarking result = constructRun(c.getPredecessorEvent(), current);
			run = run.concatenate(result.mRunInner);
			current = result.mMarking;
		}
		assert current != null;

		final ConditionMarking<LETTER, PLACE> finalMarking = current.fireEvent(event);
		final ITransition<LETTER, PLACE> t = event.getTransition();
		final PetriNetRun<LETTER, PLACE> appendix =
				new PetriNetRun<>(current.getMarking(), t.getSymbol(), finalMarking.getMarking());
		run = run.concatenate(appendix);

		mLogger.debug("Event  : " + event);
		mLogger.debug("Marking: " + run.getMarking(run.getWord().length()));
		return new RunAndConditionMarking(run, finalMarking);
	}

	private boolean parentIsCutoffEvent(final Event<LETTER, PLACE> event) {
		for (final Condition<LETTER, PLACE> c : event.getPredecessorConditions()) {
			if (c.getPredecessorEvent().isCutoffEvent()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return Some accepting run of PetriNet net, return null if net does not have an accepting run.
	 */
	public PetriNetRun<LETTER, PLACE> getAcceptingRun() {
		return mRun;
	}

	/**
	 * @return The occurrence net which is the finite prefix of the unfolding of net.
	 */
	public BranchingProcess<LETTER, PLACE> getFinitePrefix() {
		return mUnfolding;
	}

	/**
	 * Order type.
	 */
	public enum UnfoldingOrder {
		ERV("Esparza Römer Vogler"),
		KMM("Ken McMillan"),
		ERV_MARK("ERV with equal markings");

		private String mDescription;

		UnfoldingOrder(final String name) {
			mDescription = name;
		}

		public String getDescription() {
			return mDescription;
		}
	}


	public BranchingProcess<LETTER, PLACE> getResult() {
		return mUnfolding;
	}

	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataOperationCanceledException {
		if (!(mOperand instanceof IPetriNet)) {
			mLogger.warn("Will not check Unfolding because operand is constructed on-demand" );
			return true;
		}

		mLogger.info("Testing correctness of emptinessCheck");

		boolean correct;
		if (mRun == null) {
			final NestedRun<LETTER, PLACE> automataRun = (new IsEmpty<>(mServices,
					(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, (IPetriNet<LETTER, PLACE>) mOperand)).getResult())).getNestedRun();
			if (automataRun != null) {
				// TODO Christian 2016-09-30: This assignment is useless - a bug?
				correct = false;
				mLogger.error("EmptinessCheck says empty, but net accepts: " + automataRun.getWord());
			}
			correct = automataRun == null;
		} else {
			final Word<LETTER> word = mRun.getWord();
			if (new Accepts<LETTER, PLACE>(mServices, (IPetriNet<LETTER, PLACE>) mOperand, word).getResult()) {
				correct = true;
			} else {
				mLogger.error("Result of EmptinessCheck, but not accepted: " + word);
				correct = false;
			}
		}
		mLogger.info("Finished testing correctness of emptinessCheck");
		return correct;
	}

	class RunAndConditionMarking {
		private final PetriNetRun<LETTER, PLACE> mRunInner;
		private final ConditionMarking<LETTER, PLACE> mMarking;

		public RunAndConditionMarking(final PetriNetRun<LETTER, PLACE> run, final ConditionMarking<LETTER, PLACE> marking) {
			mRunInner = run;
			mMarking = marking;
		}
	}

	/**
	 * FIXME documentation.
	 */
	public class Statistics {
		private final Map<ITransition<LETTER, PLACE>, Map<Marking<LETTER, PLACE>, Set<Event<LETTER, PLACE>>>> mTrans2Mark2Events = new HashMap<>();
		private int mCutOffEvents;
		private int mNonCutOffEvents;

		public void add(final Event<LETTER, PLACE> event) {
			final Marking<LETTER, PLACE> marking = event.getMark();
			final ITransition<LETTER, PLACE> transition = event.getTransition();
			Map<Marking<LETTER, PLACE>, Set<Event<LETTER, PLACE>>> mark2Events = mTrans2Mark2Events.get(transition);
			if (mark2Events == null) {
				mark2Events = new HashMap<>();
				mTrans2Mark2Events.put(transition, mark2Events);
			}
			Set<Event<LETTER, PLACE>> events = mark2Events.get(marking);
			if (events == null) {
				events = new HashSet<>();
				mark2Events.put(marking, events);
			}
			if (!events.isEmpty()) {
				mLogger.info("inserting again Event for Transition " + transition + " and Marking " + marking);
				mLogger.info("new Event has " + event.getAncestors() + " ancestors and is "
						+ (event.isCutoffEvent() ? "" : "not ") + "cut-off event");
				for (final Event<LETTER, PLACE> event2 : events) {
					mLogger.info("  existing Event has " + event2.getAncestors() + " ancestors and is "
							+ (event.isCutoffEvent() ? "" : "not ") + "cut-off event");
					assert event2.getAncestors() == event.getAncestors() || event.isCutoffEvent();
				}
			}
			events.add(event);
			if (event.isCutoffEvent()) {
				mCutOffEvents++;
			} else {
				mNonCutOffEvents++;
			}
		}

		public String cutOffInformation() {
			return "has " + mCutOffEvents + " CutOffEvents and " + mNonCutOffEvents + " nonCutOffEvents";
		}

		public String coRelationInformation() {
			return "co relation was queried " + mUnfolding.getCoRelation().getQueryCounter() + " times.";
		}

		public long getCoRelationQueries() {
			return mUnfolding.getCoRelation().getQueryCounter();
		}

		public int getCutOffEvents() {
			return mCutOffEvents;
		}

		public int getNonCutOffEvents() {
			return mNonCutOffEvents;
		}

		/**
		 * @return Number of transitions that can never be fired in operand Petri net.
		 */
		public long unreachableTransitionsInOperand() {
			// This statistic could be computed more efficiently when using a Set<ITransition> in
			// this class' add(Event) method. But doing so would slow down computation
			// even in cases in which this statistic is not needed.
			final int transitionsInNet = ((IPetriNet<LETTER, PLACE>) mOperand).getTransitions().size();
			final long reachableTransitions = RemoveUnreachable.reachableTransitions(mUnfolding).size();
			return transitionsInNet - reachableTransitions;
		}

		public int getNumberOfUselessExtensionCandidates() {
			return ((PossibleExtensions<LETTER, PLACE>) mPossibleExtensions).getUselessExtensionCandidates();
		}

		public int getNumberOfExtensionCandidates() {
			return ((PossibleExtensions<LETTER, PLACE>) mPossibleExtensions)
					.getUsefulExtensionCandidates() + getNumberOfUselessExtensionCandidates();
		}

	}
}
