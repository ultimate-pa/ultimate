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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
public final class PetriNetUnfolder<L, P> {
	private static final boolean EXTENDED_ASSERTION_CHECKING = false;
	private static final boolean B32_OPTIMIZATION = true;
	private static final boolean USE_POR_PRUNING = true;

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final IPetriNetSuccessorProvider<L, P> mOperand;
	private final boolean mStopIfAcceptingRunFound;
	private final boolean mSameTransitionCutOff;
	private final ConfigurationOrder<L, P> mOrder;
	private final IPossibleExtensions<L, P> mPossibleExtensions;
	private final BranchingProcess<L, P> mUnfolding;
	private PetriNetRun<L, P> mRun;

	private final PetriNetUnfolder<L, P>.Statistics mStatistics = new Statistics();

	private static final boolean USE_FIRSTBORN_CUTOFF_CHECK = true;
	private static final boolean DEBUG_LOG_CO_RELATION_DEGREE_HISTOGRAM = false;

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

	public PetriNetUnfolder<L, P>.Statistics getUnfoldingStatistics() {
		return mStatistics;
	}

	private void computeUnfolding() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		boolean someInitialPlaceIsAccepting = false;
		for (final Condition<L, P> c : mUnfolding.getDummyRoot().getSuccessorConditions()) {
			if (mOperand.isAccepting(c.getPlace())) {
				someInitialPlaceIsAccepting = true;
			}
		}
		if (someInitialPlaceIsAccepting) {
			mRun = new PetriNetRun<>(
					new ConditionMarking<>(mUnfolding.getDummyRoot().getSuccessorConditions()).getMarking());
			if (mStopIfAcceptingRunFound) {
				return;
			}
		}
		mPossibleExtensions.update(mUnfolding.getDummyRoot());

		while (!mPossibleExtensions.isEmpy()) {
			final Event<L, P> e = mPossibleExtensions.remove();

			final boolean finished = computeUnfoldingHelper(e);
			if (finished) {
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
		if (USE_POR_PRUNING && isPORCutoff(event)) {
			return false;
		}

		final boolean succOfEventIsAccpting = mUnfolding.addEvent(event);
		// assert !unfolding.pairwiseConflictOrCausalRelation(e.getPredecessorConditions());
		if (succOfEventIsAccpting && mRun == null) {
			mRun = constructRun(event);
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

	/**
	 * Determines if the given event should be omitted from the unfolding, based on Partial Order Reduction reasoning.
	 * This is the case if all existing events with the same cut have independent transitions, and at least one such
	 * event already exists.
	 */
	private boolean isPORCutoff(final Event<L, P> event) {
		boolean found = false;
		for (final Event<L, P> other : mUnfolding.getEvents()) {
			if (!event.getConditionMark().equals(other.getConditionMark())) {
				continue;
			}
			found = true;

			if (!isIndependent(event.getTransition(), other.getTransition())) {
				return false;
			}
		}
		return found;
	}

	/**
	 * Determines if the given transitions are independent in a POR sense. In fact, this method goes a bit further and
	 * checks a sufficient condition that ensures that omitting one of these transitions from the unfolding still leaves
	 * a persistent set.
	 */
	private boolean isIndependent(final ITransition<L, P> t1, final ITransition<L, P> t2) {
		// Step 1: Independent transitions may not disable each other
		if (mayDisable(t1, t2) || mayDisable(t2, t1)) {
			return false;
		}

		// Step 2: If t1 and t2 are independent, then either order of firing them reaches the same marking.
		final Set<P> succ12 = jointSuccessors(t1, t2);
		final Set<P> succ21 = jointSuccessors(t2, t1);
		if (!succ12.equals(succ21)) {
			return false;
		}

		// Step 3: The intermediate markings between firing t1 and t2 (or vice versa) may not enable any transition that
		// is not also enabled before or after both have been fired.
		return !mayHideEnabledTransition(t1, t2) && !mayHideEnabledTransition(t2, t1);
	}

	/**
	 * Determines if firing one of the given transitions may disable the other.
	 *
	 * Suppose in a marking M, both transitions are enabled. Then we can write M = core(M) ∪ pre(t1) ∪ pre(t2), where
	 * core(M) = M \ (pre(t1) ∪ pre(t2)).
	 *
	 * After firing t1, we reach a marking M1 = core(M) ∪ pre(t2)\pre(t1) ∪ suc(t1). In order for t2 to still be enabled
	 * in M1, we must thus check that all the common predecessors of t1 and t2 are also successors of t1.
	 */
	private boolean mayDisable(final ITransition<L, P> t1, final ITransition<L, P> t2) {
		final Set<P> t1Pre = mOperand.getPredecessors(t1);
		final Set<P> t2Pre = mOperand.getPredecessors(t2);
		final Set<P> t1Succ = mOperand.getSuccessors(t1);

		return !t2Pre.stream().filter(t1Pre::contains).allMatch(t1Succ::contains);
	}

	/**
	 * Computes the set of all "new" successor places reached after firing t1 and then t2, assuming t1 does not disable
	 * t2; i.e., all successor places that are not necessarily present in the original marking.
	 *
	 * Suppose in a marking M, both transitions are enabled. Then we can write M = core(M) ∪ pre(t1) ∪ pre(t2), where
	 * core(M) = M \ (pre(t1) ∪ pre(t2)).
	 *
	 * After firing t1, we reach a marking M1 = core(M) ∪ pre(t2)\pre(t1) ∪ suc(t1). If t2 is still enabled and fired
	 * from this marking, we reach the marking core(M) ∪ suc(t1)\pre(t2) ∪ suc(t2).
	 *
	 * Hence, this method computes the set suc(t1)\pre(t2) ∪ suc(t2).
	 */
	private Set<P> jointSuccessors(final ITransition<L, P> t1, final ITransition<L, P> t2) {
		final Set<P> t1Succ = mOperand.getSuccessors(t1);
		final Set<P> t2Pre = mOperand.getPredecessors(t2);
		final Set<P> t2Succ = mOperand.getSuccessors(t2);

		return DataStructureUtils.union(DataStructureUtils.difference(t1Succ, t2Pre), t2Succ);
	}

	/**
	 * Determines if firing t1 may enable a transition that is neither enabled before firing t1, nor after both t1 and
	 * t2 have been fired; assuming t1 and t2 don't disable each other and reach the same successors after both have
	 * been fired. We say that t3 is "hidden".
	 *
	 * Suppose in a marking M, both transitions are enabled. Then we can write M = core(M) ∪ pre(t1) ∪ pre(t2), where
	 * core(M) = M \ (pre(t1) ∪ pre(t2)). After firing t1, we reach a marking M1 = core(M) ∪ pre(t2)\pre(t1) ∪ suc(t1).
	 * Suppose now some transition t3 was enabled in M1.
	 *
	 * If pre(t3) ⊆ core(M) ∪ pre(t2)\pre(t1), then also pre(t3) ⊆ M and the transition is thus not hidden (it is
	 * enabled already before t1 is ever fired).
	 *
	 * If on the other hand pre(t3) ⊆ core(M) ∪ suc(t1), then t3 is enabled after firing both t2 and then t1. By
	 * assumption, it is then also enabled after firing first t1 and then t2. Hence t3 is not hidden in this case
	 * either.
	 *
	 * Only in the remaining case, where pre(t3) contains at least one place in pre(t1)\pre(t1) and at least one place
	 * in suc(t1), t3 may be hidden. Hence we check here if such a t3 exists.
	 */
	private boolean mayHideEnabledTransition(final ITransition<L, P> t1, final ITransition<L, P> t2) {
		final Set<P> t1Pre = mOperand.getPredecessors(t1);
		final Set<P> t2Pre = mOperand.getPredecessors(t2);
		final Set<P> t1Succ = mOperand.getSuccessors(t1);
		final Set<P> intermediatePre = DataStructureUtils.difference(t2Pre, t1Pre);

		final Set<P> possiblePlaces = DataStructureUtils.union(t1Succ, intermediatePre);
		final Collection<ISuccessorTransitionProvider<L, P>> candidates =
				mOperand.getSuccessorTransitionProviders(t1Succ, possiblePlaces);

		for (final ISuccessorTransitionProvider<L, P> candidate : candidates) {
			if (candidate.getPredecessorPlaces().stream().anyMatch(intermediatePre::contains)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * constructs a run over the unfolding which leads to the marking corresponding with the local configuration of the
	 * specified event e.
	 * <p>
	 * uses the recursive helper-method {@code #constructRun(Event, Marking)}
	 */
	private PetriNetRun<L, P> constructRun(final Event<L, P> event) {
		mLogger.debug("Marking: " + mUnfolding.getDummyRoot().getMark());
		try {
			return constructRun(event, mUnfolding.getDummyRoot().getConditionMark()).mRunInner;
		} catch (final PetriNetNot1SafeException e) {
			throw new AssertionError("Petri net not one safe for places " + e.getUnsafePlaces()
					+ " but this should have been detected earlier.");
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
		final ITransition<L, P> t = event.getTransition();
		final PetriNetRun<L, P> appendix =
				new PetriNetRun<>(current.getMarking(), t.getSymbol(), finalMarking.getMarking());
		run = run.concatenate(appendix);

		mLogger.debug("Event  : " + event);
		mLogger.debug("Marking: " + run.getMarking(run.getWord().length()));
		return new RunAndConditionMarking(run, finalMarking);
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
	 * @return Some accepting run of PetriNet net, return null if net does not have an accepting run.
	 */
	public PetriNetRun<L, P> getAcceptingRun() {
		return mRun;
	}

	/**
	 * @return The occurrence net which is the finite prefix of the unfolding of net.
	 */
	public BranchingProcess<L, P> getFinitePrefix() {
		return mUnfolding;
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

	public BranchingProcess<L, P> getResult() {
		return mUnfolding;
	}

	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<P> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		if (!(mOperand instanceof IPetriNet)) {
			mLogger.warn("Will not check Unfolding because operand is constructed on-demand");
			return true;
		}

		mLogger.info("Testing correctness of emptinessCheck");

		boolean correct;
		if (mRun == null) {
			final NestedRun<L, P> automataRun = (new IsEmpty<>(mServices,
					(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, (IPetriNet<L, P>) mOperand)).getResult()))
							.getNestedRun();
			if (automataRun != null) {
				// TODO Christian 2016-09-30: This assignment is useless - a bug?
				correct = false;
				mLogger.error("EmptinessCheck says empty, but net accepts: " + automataRun.getWord());
			}
			correct = automataRun == null;
		} else {
			final Word<L> word = mRun.getWord();
			if (new Accepts<>(mServices, (IPetriNet<L, P>) mOperand, word).getResult()) {
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
		private final PetriNetRun<L, P> mRunInner;
		private final ConditionMarking<L, P> mMarking;

		public RunAndConditionMarking(final PetriNetRun<L, P> run, final ConditionMarking<L, P> marking) {
			mRunInner = run;
			mMarking = marking;
		}
	}

	/**
	 * FIXME documentation.
	 */
	public class Statistics {
		private final Map<ITransition<L, P>, Map<Marking<L, P>, Set<Event<L, P>>>> mTrans2Mark2Events = new HashMap<>();
		private int mCutOffEvents;
		private int mNonCutOffEvents;

		public void add(final Event<L, P> event) {
			// TODO: The hash operations here take A LOT of time (~20% on the VMCAI2021) benchmarks
			final Marking<L, P> marking = event.getMark();
			final ITransition<L, P> transition = event.getTransition();
			Map<Marking<L, P>, Set<Event<L, P>>> mark2Events = mTrans2Mark2Events.get(transition);
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
			// This statistic could be computed more efficiently when using a Set<ITransition> in
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
