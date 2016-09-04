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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class PetriNetUnfolder<S, C> extends UnaryNetOperation<S, C> {

	private final boolean mStopIfAcceptingRunFound;
	private final boolean mSameTransitionCutOff;
	private final order mOrder;
	private final IPossibleExtensions<S, C> mPossibleExtensions;
	private final BranchingProcess<S, C> mUnfolding;
	private PetriNetRun<S, C> mRun;

	private final Order<S, C> mMcMillanOrder = new Order<S, C>() {
		@Override
		public int compare(final Configuration<S, C> o1, final Configuration<S, C> o2) {
			return o1.size() - o2.size();
		}
	};

	private final Order<S, C> mEsparzaRoemerVoglerOrder = new Order<S, C>() {

		@Override
		public int compare(final Configuration<S, C> c1, final Configuration<S, C> c2) {
			int result = c1.compareTo(c2);
			if (result != 0) {
				return result;
			}
			final Configuration<S, C> min1 = c1.getMin(mUnfolding);
			final Configuration<S, C> min2 = c2.getMin(mUnfolding);
			result = min1.compareTo(min2);
			if (result != 0) {
				return result;
			}
			final Configuration<S, C> c1withoutMin1 = c1.removeMin();
			final Configuration<S, C> c2withoutMin2 = c2.removeMin();

			assert (c1.equals(c2) || !c1withoutMin1.equals(c2withoutMin2)) : "\ne1\t="
					+ c1
					+ "\ne2\t="
					+ c2
					+ "\nmin1\t="
					+ min1
					+ "\nmin2\t="
					+ min2
					+ "\n-min1\t="
					+ c1withoutMin1
					+ "\n-min2\t="
					+ c2withoutMin2;

			// The Arguments are here technically no longer Configurations but
			// the lexicographical extension of the order on transitions which
			// is implemented in the compareTo method works on Sets of Events.
			// See 1996TACAS - Esparza,Römer,Vogler, page 13.
			result = compare(c1withoutMin1, c2withoutMin2);
			// result = e1withoutMin1.compareTo(e2withoutMin2);
			return result;
		}
	};

	private final Order<S, C> mErvEqualMarkingOrder = new Order<S, C>() {

		@Override
		public int compare(final Event<S, C> o1, final Event<S, C> o2) {
			int result = mMcMillanOrder.compare(o1, o2);
			if (result != 0) {
				return result;
			}
			if (!o1.getMark().equals(o2.getMark())) {
				return 0;
			}
			final Configuration<S, C> c1 = o1.getLocalConfiguration();
			final Configuration<S, C> c2 = o2.getLocalConfiguration();
			assert !(c1.containsAll(c2) && c2.containsAll(c1)) :
				"Different events with equal local configurations. equals:"
					+ c1.equals(c2);
			result = compare(c1, c2);

			return result;
		}

		@Override
		public int compare(final Configuration<S, C> c1, final Configuration<S, C> c2) {
			return mEsparzaRoemerVoglerOrder.compare(c1, c2);
		}
	};
	
	private final PetriNetUnfolder<S, C>.Statistics mStatistics = new Statistics();

	/**
	 * Build the finite Prefix of PetriNet net.
	 * 
	 * @param services Ultimate services
	 * @param operand Petri net
	 * @param order
	 *            the order on events and configurations respectively is used to
	 *            determine cut-off events.
	 * @param sameTransitionCutOff
	 *            if true, an additional condition for cut-off events is used:
	 *            An event and its companion must belong to the same transition
	 *            from the net.
	 * @param stopIfAcceptingRunFound
	 *            if false, the complete finite Prefix will be build.
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public PetriNetUnfolder(final AutomataLibraryServices services,
			final PetriNetJulian<S, C> operand, final order order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException {
		super(services, operand);
		this.mStopIfAcceptingRunFound = stopIfAcceptingRunFound;
		this.mSameTransitionCutOff = sameTransitionCutOff;
		this.mOrder = order;
		mLogger.info(startMessage());
		this.mUnfolding = new BranchingProcess<S, C>(mServices, operand, mEsparzaRoemerVoglerOrder);
		// this.cutOffEvents = new HashSet<Event<S, C>>();
		Order<S, C> queueOrder = mMcMillanOrder;
		switch (order) {
		case ERV_MARK:
			queueOrder = mErvEqualMarkingOrder;
			break;
		case ERV:
			queueOrder = mEsparzaRoemerVoglerOrder;
			break;
		default:
			throw new IllegalArgumentException();
		}
		this.mPossibleExtensions = new PossibleExtensions<S, C>(mUnfolding,
				queueOrder);

		computeUnfolding();
		mLogger.info(exitMessage());
		mLogger.info(mStatistics.cutOffInformation());
		mLogger.info(mStatistics.coRelationInformation());
	}
	
	@Override
	public String operationName() {
		return "finitePrefix";
	}

	@Override
	public String startMessage() {
		return "Start "
				+ operationName()
				+ ". Net "
				+ mOperand.sizeInformation()
				+ (mStopIfAcceptingRunFound ? "We stop if some accepting run was found"
						: "We compute complete finite Prefix");
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ mUnfolding.sizeInformation();
	}

	private void computeUnfolding() throws AutomataOperationCanceledException {
		mPossibleExtensions.update(mUnfolding.getDummyRoot());

		while (!mPossibleExtensions.isEmpy()) {
			final Event<S, C> e = mPossibleExtensions.remove();

			if (!parentIsCutoffEvent(e)) {
				final boolean succOfEventIsAccpting = mUnfolding.addEvent(e);
				// assert !unfolding.pairwiseConflictOrCausalRelation(
				// e.getPredecessorConditions());
				if (succOfEventIsAccpting && mRun == null) {
					mRun = constructRun(e);
					if (mStopIfAcceptingRunFound) {
						return;
					}
				}
				// TODO: switch over the order given in the constructor.
				if (!mUnfolding.isCutoffEvent(e, mEsparzaRoemerVoglerOrder,
						mSameTransitionCutOff)) {
					mPossibleExtensions.update(e);
					mLogger.debug("Constructed Non-cut-off-Event: "
							+ e.toString());
				} else {
					mLogger.debug("Constructed     Cut-off-Event: "
							+ e.toString());
				}
				mLogger.debug("Possible Extension size: "
						+ mPossibleExtensions.size() + ", total #Events: "
						+ mUnfolding.getEvents().size()
						+ ", total #Conditions: "
						+ mUnfolding.getConditions().size());
				mStatistics.add(e);
			}
			// else {
			// assert (false);
			// }

			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
	}

	/**
	 * constructs a run over the unfolding which leads to the marking
	 * corresponding with the local configuration of the specified event e.
	 * 
	 * <p>uses the recursive helper-method {@code #constructRun(Event, Marking)}
	 */
	private PetriNetRun<S, C> constructRun(final Event<S, C> e) {
		mLogger.debug("Marking: " + mUnfolding.getDummyRoot().getMark());
		return constructRun(e, mUnfolding.getDummyRoot().getConditionMark()).mRun;
	}

	/**
	 * Recursively builds a part of a run over the unfolding which leads to the
	 * marking corresponding with the local configuration of the specified event
	 * e.
	 * 
	 * <p>The run starts with the given Marking {@code initialMarking}
	 */
	private RunAndConditionMarking constructRun(final Event<S, C> e,
			final ConditionMarking<S, C> initialMarking) {
		assert (e != mUnfolding.getDummyRoot());
		assert (e.getPredecessorConditions().size() > 0);
		assert !mUnfolding.pairwiseConflictOrCausalRelation(e
				.getPredecessorConditions());
		PetriNetRun<S, C> run = new PetriNetRun<S, C>(
				initialMarking.getMarking());
		ConditionMarking<S, C> current = initialMarking;
		for (final Condition<S, C> c : e.getPredecessorConditions()) {
			if (current.contains(c)) {
				continue;
			}
			final RunAndConditionMarking result = constructRun(
					c.getPredecessorEvent(), current);
			run = run.concatenate(result.mRun);
			current = result.mMarking;
		}
		assert (current != null);

		final ConditionMarking<S, C> finalMarking = current.fireEvent(e);
		final ITransition<S, C> t = e.getTransition();
		final PetriNetRun<S, C> appendix = new PetriNetRun<S, C>(
				current.getMarking(), t.getSymbol(), finalMarking.getMarking());
		run = run.concatenate(appendix);

		mLogger.debug("Event  : " + e);
		mLogger.debug("Marking: " + run.getMarking(run.getWord().length()));
		return new RunAndConditionMarking(run, finalMarking);
	}

	class RunAndConditionMarking {
		public PetriNetRun<S, C> mRun;
		public ConditionMarking<S, C> mMarking;
		
		public RunAndConditionMarking(final PetriNetRun<S, C> run,
				final ConditionMarking<S, C> marking) {
			mRun = run;
			mMarking = marking;
		}
	}

	private boolean parentIsCutoffEvent(final Event<S, C> e) {
		for (final Condition<S, C> c : e.getPredecessorConditions()) {
			if (c.getPredecessorEvent().isCutoffEvent()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Return some accepting run of PetriNet net, return null if net does not
	 * have an accepting run.
	 */
	public PetriNetRun<S, C> getAcceptingRun() throws AutomataOperationCanceledException, AssertionError {
		return mRun;
	}

	/**
	 * Return the occurrence net which is the finite prefix of the unfolding of
	 * net.
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public BranchingProcess<S, C> getFinitePrefix() throws AutomataOperationCanceledException {
		return mUnfolding;
	}

	/**
	 * Return an PetriNet that recognizes the same language as net but has a a
	 * similar structure as the occurrence net which is the finite prefix of
	 * net.
	 */
	// TODO Julian and Matthias have to discuss what similar means.
	public PetriNetJulian<S, C> getUnfoldedPetriNet() {
		return null;
	}

	public enum order {
		ERV("Esparza Römer Vogler"), KMM("Ken McMillan"), ERV_MARK(
				"ERV with equal markings");

		private String mDescription;

		private order(final String name) {
			mDescription = name;
		}

		public String getDescription() {
			return mDescription;
		}
	}

	// FIXME documentation
	private class Statistics {
		private final Map<ITransition<S, C>, Map<Marking<S, C>, Set<Event<S, C>>>> mTrans2Mark2Events =
				new HashMap<ITransition<S, C>, Map<Marking<S, C>, Set<Event<S, C>>>>();
		private int mCutOffEvents = 0;
		private int mNonCutOffEvents = 0;

		public void add(final Event<S, C> e) {
			final Marking<S, C> marking = e.getMark();
			final ITransition<S, C> transition = e.getTransition();
			Map<Marking<S, C>, Set<Event<S, C>>> mark2Events = mTrans2Mark2Events
					.get(transition);
			if (mark2Events == null) {
				mark2Events = new HashMap<Marking<S, C>, Set<Event<S, C>>>();
				mTrans2Mark2Events.put(transition, mark2Events);
			}
			Set<Event<S, C>> events = mark2Events.get(marking);
			if (events == null) {
				events = new HashSet<Event<S, C>>();
				mark2Events.put(marking, events);
			}
			if (!events.isEmpty()) {
				mLogger.info("inserting again Event for Transition "
						+ transition + " and Marking " + marking);
				mLogger.info("new Event has " + e.getAncestors()
						+ " ancestors and is "
						+ (e.isCutoffEvent() ? "" : "not ") + "cut-off event");
				for (final Event<S, C> event : events) {
					mLogger.info("  existing Event has "
							+ event.getAncestors() + " ancestors and is "
							+ (e.isCutoffEvent() ? "" : "not ")
							+ "cut-off event");
					assert (event.getAncestors() == e.getAncestors() | e
							.isCutoffEvent());
				}
			}
			events.add(e);

			if (e.isCutoffEvent()) {
				mCutOffEvents++;
			} else {
				mNonCutOffEvents++;
			}

		}

		public String cutOffInformation() {
			return "has " + mCutOffEvents + " CutOffEvents and "
					+ mNonCutOffEvents + " nonCutOffEvents";
		}

		public String coRelationInformation() {
			return "co relation was queried "
					+ mUnfolding.getCoRelationQueries() + " times.";
		}
	}

	@Override
	public BranchingProcess<S, C> getResult() {
		return mUnfolding;
	}

	@Override
	public boolean checkResult(final IStateFactory<C> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Testing correctness of emptinessCheck");

		boolean correct = true;
		if (mRun == null) {
			final NestedRun<S, C> automataRun =
					(new IsEmpty<S, C>(mServices,
							(new PetriNet2FiniteAutomaton<S, C>(mServices, mOperand)).getResult())).getNestedRun();
			if (automataRun != null) {
				correct = false;
				mLogger.error("EmptinessCheck says empty, but net accepts: " + automataRun.getWord());
			}
			correct = (automataRun == null);
		} else {
			final Word<S> word = mRun.getWord();
			if (mOperand.accepts(word)) {
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
