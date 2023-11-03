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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

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
public abstract class PetriNetUnfolderBase<L, P, R> {
	protected static final boolean EXTENDED_ASSERTION_CHECKING = false;
	private static final boolean B32_OPTIMIZATION = true;

	private static final boolean USE_FIRSTBORN_CUTOFF_CHECK = true;
	private static final boolean DEBUG_LOG_CO_RELATION_DEGREE_HISTOGRAM = false;

	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;

	protected final IPetriNetSuccessorProvider<L, P> mOperand;
	private final boolean mStopIfAcceptingRunFound;
	private final boolean mSameTransitionCutOff;
	private final ConfigurationOrder<L, P> mOrder;
	private final IPossibleExtensions<L, P> mPossibleExtensions;
	protected final BranchingProcess<L, P> mUnfolding;
	private R mRun;

	private final Statistics mStatistics = new Statistics();

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
	public PetriNetUnfolderBase(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<L, P> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
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
		case ERV:
			mOrder = new EsparzaRoemerVoglerOrder<>();
			break;
		case DBO:
			mOrder = new DepthBasedOrder<>();
			break;
		default:
			throw new IllegalArgumentException();
		}
		mUnfolding = new BranchingProcess<>(mServices, operand, mOrder, USE_FIRSTBORN_CUTOFF_CHECK, B32_OPTIMIZATION);
		mPossibleExtensions =
				new PossibleExtensions<>(mUnfolding, mOrder, USE_FIRSTBORN_CUTOFF_CHECK, B32_OPTIMIZATION);

		computeUnfolding();
		mLogger.info(mStatistics.prettyprintCutOffInformation());
		mLogger.info(mStatistics.prettyprintCoRelationInformation());
		if (DEBUG_LOG_CO_RELATION_DEGREE_HISTOGRAM) {
			final TreeHashRelation<Integer, Condition<L, P>> histogram =
					mUnfolding.getCoRelation().computeHistogramOfDegree(mUnfolding.getConditions());
			final StringBuilder sb = new StringBuilder();
			sb.append("Histogram of co-relation degrees:" + System.lineSeparator());
			for (final Entry<Integer, Condition<L, P>> pair : histogram.getSetOfPairs()) {
				sb.append("Degree " + pair.getKey() + ": " + pair.getValue());
				sb.append(System.lineSeparator());
			}
			mLogger.info(sb.toString());
		}
	}

	public Statistics getUnfoldingStatistics() {
		return mStatistics;
	}

	/**
	 * @return Some accepting run of PetriNet net, return null if net does not have an accepting run.
	 */
	public R getAcceptingRun() {
		return mRun;
	}

	/**
	 * Checks the initial places of the Unfolding for a valid run/word.
	 *
	 * @return bool if word is found
	 * @throws PetriNetNot1SafeException
	 */
	protected abstract boolean checkInitialPlaces();

	protected abstract R constructInitialRun() throws PetriNetNot1SafeException;

	/**
	 * Adds the event to the Unfolding and then checks if a word can be found in this new Unfolding.
	 *
	 * @param event
	 * @return bool if word is found
	 * @throws PetriNetNot1SafeException
	 */
	protected abstract boolean addAndCheck(final Event<L, P> event) throws PetriNetNot1SafeException;

	protected abstract R constructRun(final Event<L, P> event) throws PetriNetNot1SafeException;

	private void computeUnfolding() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		if (checkInitialPlaces()) {
			mRun = constructInitialRun();
			if (mStopIfAcceptingRunFound) {
				return;
			}
		}
		mPossibleExtensions.update(mUnfolding.getDummyRoot());

		while (!mPossibleExtensions.isEmpy()) {
			final Event<L, P> e = mPossibleExtensions.remove();

			final boolean finished = computeUnfoldingHelper(e);
			if (finished) {
				mLogger.info("Found word, exiting Unfolder.");
				return;
			}

			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
						"constructing finite prefix that currently has " + mUnfolding.getConditions().size()
								+ " conditions, " + mUnfolding.getEvents().size() + " events ("
								+ mStatistics.prettyprintCutOffInformation() + " "
								+ mStatistics.prettyprintCoRelationInformation() + " "
								+ mStatistics.prettyprintPossibleExtensionsMaximalSize() + " "
								+ mStatistics.prettyprintNumberOfEventComparisons() + " "
								+ mStatistics.prettyprintPossibleExtensionCandidatesInformation() + " "
								+ mStatistics.prettyprintCoRelationMaximalDegree() + " "
								+ mStatistics.prettyprintConditionPerPlaceMax() + ")");
				throw new AutomataOperationCanceledException(rti);
			}
		}
	}

	private boolean computeUnfoldingHelper(final Event<L, P> event) throws PetriNetNot1SafeException {
		assert !parentIsCutoffEvent(event) : "We must not construct successors of cut-off events.";
		boolean isCutOffEvent;
		if (!USE_FIRSTBORN_CUTOFF_CHECK) {
			isCutOffEvent = mUnfolding.isCutoffEvent(event, mOrder, mSameTransitionCutOff);
		} else {
			isCutOffEvent = event.isCutoffEvent();
		}
		if (addAndCheck(event)) {
			if (mRun == null) {
				mRun = constructRun(event);
			}
			if (mStopIfAcceptingRunFound) {
				return true;
			}
		}

		if (isCutOffEvent) {
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

	private boolean parentIsCutoffEvent(final Event<L, P> event) {
		for (final Condition<L, P> c : event.getPredecessorConditions()) {
			if (c.getPredecessorEvent().isCutoffEvent()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return The occurrence net which is the finite prefix of the unfolding of net.
	 */
	public BranchingProcess<L, P> getFinitePrefix() {
		return mUnfolding;
	}

	public BranchingProcess<L, P> getResult() {
		return mUnfolding;
	}

	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<P> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		return checkRun(stateFactory, mRun);
	}

	protected abstract boolean checkRun(IPetriNet2FiniteAutomatonStateFactory<P> stateFactory, R run)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException;

	/**
	 * FIXME documentation.
	 */
	public class Statistics {
		private final Map<Transition<L, P>, Map<Marking<P>, Set<Event<L, P>>>> mTrans2Mark2Events = new HashMap<>();
		private int mCutOffEvents;
		private int mNonCutOffEvents;

		public void add(final Event<L, P> event) {
			// TODO: The hash operations here take A LOT of time (~20% on the VMCAI2021) benchmarks
			final Marking<P> marking = event.getMark();
			final Transition<L, P> transition = event.getTransition();
			Map<Marking<P>, Set<Event<L, P>>> mark2Events = mTrans2Mark2Events.get(transition);
			if (mark2Events == null) {
				mark2Events = new HashMap<>();
				mTrans2Mark2Events.put(transition, mark2Events);
			}
			Set<Event<L, P>> events = mark2Events.get(marking);
			if (events == null) {
				events = new HashSet<>();
				mark2Events.put(marking, events);
			}
			if (events.size() > 2) {
				// 2019-12-15 Matthias: Adding an event twice for a transition-marking pair is
				// very natural.
				// We write log messages only if an event was added three or more times. This
				// can even happen for total orders
				mLogger.info("inserting event number " + (events.size() + 1) + " for the transition-marking pair ("
						+ transition + ", " + marking + ")");
				mLogger.info("this new event has " + event.getAncestors() + " ancestors and is "
						+ (event.isCutoffEvent() ? "" : "not ") + "cut-off event");
				for (final Event<L, P> event2 : events) {
					mLogger.info("  existing Event has " + event2.getAncestors() + " ancestors and is "
							+ (event.isCutoffEvent() ? "" : "not ") + "cut-off event");
					assert event2.getAncestors() == event.getAncestors() || event.isCutoffEvent()
							|| event2.isCutoffEvent() : "if there is "
									+ "already an event that has the same marking and a different size of "
									+ "local configuration then the new event must be cut-off event";
				}
			}
			events.add(event);
			if (event.isCutoffEvent()) {
				mCutOffEvents++;
			} else {
				mNonCutOffEvents++;
			}
		}

		public String prettyprintCutOffInformation() {
			return getCutOffEvents() + "/" + (getCutOffEvents() + getNonCutOffEvents()) + " cut-off events.";
		}

		public String prettyprintCoRelationInformation() {
			return "For " + getCoRelationQueriesYes() + "/" + (getCoRelationQueriesYes() + getCoRelationQueriesNo())
					+ " co-relation queries the response was YES.";
		}

		public String prettyprintPossibleExtensionCandidatesInformation() {
			return getNumberOfUselessExtensionCandidates() + "/" + getNumberOfExtensionCandidates()
					+ " useless extension candidates.";
		}

		public String prettyprintPossibleExtensionsMaximalSize() {
			return "Maximal size of possible extension queue " + getMaximalSizeOfPossibleExtensions() + ".";
		}

		public String prettyprintCoRelationMaximalDegree() {
			return "Maximal degree in co-relation " + computeCoRelationMaximalDegree() + ".";
		}

		public String prettyprintConditionPerPlaceMax() {
			return "Up to " + computeConditionPerPlaceMax() + " conditions per place.";
		}

		public String prettyprintNumberOfEventComparisons() {
			return "Compared " + getNumberOfConfigurationComparisons() + " event pairs, "
					+ getNumberOfFoataBasedConfigurationComparisons() + " based on Foata normal form.";
		}

		public long getCoRelationQueriesYes() {
			return mUnfolding.getCoRelation().getQueryCounterYes();
		}

		public long getCoRelationQueriesNo() {
			return mUnfolding.getCoRelation().getQueryCounterNo();
		}

		public int getCutOffEvents() {
			return mCutOffEvents;
		}

		public int getNonCutOffEvents() {
			return mNonCutOffEvents;
		}

		public int getNumberOfConfigurationComparisons() {
			return mOrder.getNumberOfComparisons();
		}

		public int getNumberOfFoataBasedConfigurationComparisons() {
			return mOrder.getFotateNormalFormComparisons();
		}

		/**
		 * @return Number of transitions that can never be fired in operand Petri net.
		 */
		public long unreachableTransitionsInOperand() {
			// This statistic could be computed more efficiently when using a Set<Transition> in
			// this class' add(Event) method. But doing so would slow down computation
			// even in cases in which this statistic is not needed.
			final int transitionsInNet = ((IPetriNet<L, P>) mOperand).getTransitions().size();
			final long reachableTransitions = RemoveUnreachable.reachableTransitions(mUnfolding).size();
			return transitionsInNet - reachableTransitions;
		}

		public int getNumberOfUselessExtensionCandidates() {
			return mPossibleExtensions.getUselessExtensionCandidates();
		}

		public int getNumberOfExtensionCandidates() {
			return mPossibleExtensions.getUsefulExtensionCandidates() + getNumberOfUselessExtensionCandidates();
		}

		public int computeCoRelationMaximalDegree() {
			return mUnfolding.getCoRelation().computeMaximalDegree();
		}

		public int computeConditionPerPlaceMax() {
			return mUnfolding.computeConditionPerPlaceMax();
		}

		public int getMaximalSizeOfPossibleExtensions() {
			return mPossibleExtensions.getMaximalSize();
		}

	}
}
