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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class BranchingProcess<LETTER, PLACE> implements IAutomaton<LETTER, PLACE> {
	/**
	 * Before 2019-10-20 we added cut-off events and their successor conditions to the co-relation. This is not
	 * necessary for the computation of the finite prefix (maybe necessary for other applications) and we might be able
	 * to save some time. See Issue #448. https://github.com/ultimate-pa/ultimate/issues/448
	 */
	private static final boolean ADD_CUTOFF_EVENTS_TO_CORELATION = true;
	private final AutomataLibraryServices mServices;

	private final Collection<Condition<LETTER, PLACE>> mConditions;
	private final Collection<Event<LETTER, PLACE>> mEvents;

	private final ICoRelation<LETTER, PLACE> mCoRelation;

	private final HashRelation<PLACE, Condition<LETTER, PLACE>> mPlace2Conds;

	/**
	 * Dummy root event with all initial conditions as successors. Unlike all other events in this branching process,
	 * the root does not correspond to any transition of {@link #mNet}.
	 */
	private final Event<LETTER, PLACE> mDummyRoot;

	/**
	 * Net associated with this branching process. Places of this branching process correspond to places of the net.
	 * Events of this branching process correspond to transitions of the net.
	 */
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mNet;

	/**
	 * The input is a {@link IPetriNetSuccessorProvider} and does not provide the predecessor transitions of places. We
	 * use this relation to store the information that we observed while computing the finite prefix.
	 */
	private final HashRelation<PLACE, Transition<LETTER, PLACE>> mYetKnownPredecessorTransitions = new HashRelation<>();

	private final ConfigurationOrder<LETTER, PLACE> mOrder;

	private int mConditionSerialnumberCounter;

	/**
	 * Relation between the hashcode of {@link Event} {@link Marking}s and all non-cut-off Events that have this
	 * {@link Marking}. Hashcode is the key, allows us to check find cut-off events more quickly.
	 * <p>
	 * 2019-11-16 Matthias: I have some doubts that this optimization (hashcode instead of {@link Marking}) brings a
	 * measureable speedup but it makes the code more complicated. I case we have total {@link ConfigurationOrder} the
	 * image of the relation has size one and hence we could use a map instead of a relation. I guess that using a map
	 * instead of a relation will not bring a significant speedup and will only reduce the memory consumption by 64 byes
	 * (initial size of HashSet) per non-cut-off event.
	 * </p>
	 */
	private final HashRelation<Integer, Event<LETTER, PLACE>> mMarkingNonCutoffEventRelation = new HashRelation<>();

	/**
	 * #Backfolding Temporary boolean flag for testing our computation of a "finite comprehensive prefix".
	 */
	private final boolean mNewFiniteComprehensivePrefixMode = false;
	private final boolean mUseFirstbornCutoffCheck;

	public Set<Event<LETTER, PLACE>> mCutoffEvents = new HashSet<>();

	public BranchingProcess(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, PLACE> net,
			final ConfigurationOrder<LETTER, PLACE> order, final boolean useCutoffChekingPossibleExtention,
			final boolean useB32Optimization) throws PetriNetNot1SafeException {
		mServices = services;
		mNet = net;
		mOrder = order;
		mPlace2Conds = new HashRelation<>();
		mConditions = new HashSet<>();
		mEvents = new HashSet<>();
		if (useB32Optimization) {
			mCoRelation = new ConditionEventsCoRelationB32<>(this);
		} else {
			mCoRelation = new ConditionEventsCoRelation<>(this);
		}

		mUseFirstbornCutoffCheck = useCutoffChekingPossibleExtention;

		// add a dummy event as root. its successors are the initial conditions.
		mDummyRoot = new Event<>(this);
		// mCoRelation.initialize(mDummyRoot.getSuccessorConditions());
		addEvent(mDummyRoot);
	}

	/**
	 * @return dummy root event with all initial conditions as successors. Is not associated with any transition from
	 *         the net.
	 */
	public Event<LETTER, PLACE> getDummyRoot() {
		return mDummyRoot;
	}

	public Condition<LETTER, PLACE> constructCondition(final Event<LETTER, PLACE> predecessor, final PLACE place) {
		return new Condition<>(predecessor, place, mConditionSerialnumberCounter++);
	}

	/**
	 * Adds an Event to the Branching Process with all outgoing Conditions.
	 * <p>
	 * updates the Co-Relation.
	 * </p>
	 *
	 * @param event
	 *            event
	 * @return true iff some successor of e corresponds to an accepting place
	 * @throws PetriNetNot1SafeException
	 */
	boolean addEvent(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		if (event != getDummyRoot()) {
			for (final Condition<LETTER, PLACE> c : event.getSuccessorConditions()) {
				mYetKnownPredecessorTransitions.addPair(c.getPlace(), event.getTransition());
			}
		}
		if (event.isCutoffEvent()) {
			mCutoffEvents.add(event);
		}
		event.setSerialNumber(mEvents.size());
		mEvents.add(event);
		if (!mUseFirstbornCutoffCheck && !event.isCutoffEvent()) {
			mMarkingNonCutoffEventRelation.addPair(event.getMark().hashCode(), event);
		}
		for (final Condition<LETTER, PLACE> c : event.getPredecessorConditions()) {
			assert !c.getPredecessorEvent().isCutoffEvent() : "Cut-off events must not have successors.";
			c.addSuccesssor(event);
		}
		boolean someSuccessorIsAccepting = false;
		for (final Condition<LETTER, PLACE> c : event.getSuccessorConditions()) {
			mConditions.add(c);
			mPlace2Conds.addPair(c.getPlace(), c);
			if (mNet.isAccepting(c.getPlace())) {
				someSuccessorIsAccepting = true;
			}
		}
		if (ADD_CUTOFF_EVENTS_TO_CORELATION || !event.isCutoffEvent()) {
			mCoRelation.update(event);
		}
		return someSuccessorIsAccepting;
	}

	/**
	 * Checks if a new event {@code event}, with regards to {@code order} is a cut-off event. In that case, companions
	 * are computed as a side-effect.
	 *
	 * @param event
	 *            event
	 * @param order
	 *            order
	 * @param sameTransitionCutOff
	 *            {@code true} iff events belong to the same transition
	 * @return true iff event is cut-off
	 * @see Event#checkCutOffAndSetCompanion(Event, Comparator, boolean)
	 */
	public boolean isCutoffEvent(final Event<LETTER, PLACE> event, final Comparator<Event<LETTER, PLACE>> order,
			final boolean sameTransitionCutOff) {
		for (final Event<LETTER, PLACE> ev : mMarkingNonCutoffEventRelation.getImage(event.getMark().hashCode())) {
			if (mNewFiniteComprehensivePrefixMode) {
				if (event.checkCutOffAndSetCompanionForComprehensivePrefix(ev, order, sameTransitionCutOff)) {
					return true;
				}
			} else if (event.checkCutOffAndSetCompanion(ev, order, sameTransitionCutOff)) {
				return true;
			}
		}
		return false;
	}

	public Set<Event<LETTER, PLACE>> getCutoffEvents() {
		return mCutoffEvents;
	}

	/**
	 * @param place
	 *            place
	 * @return all conditions c s.t. p is the corresponding place of c.
	 */
	public Set<Condition<LETTER, PLACE>> place2cond(final PLACE place) {
		return mPlace2Conds.getImage(place);
	}

	public ICoRelation<LETTER, PLACE> getCoRelation() {
		return mCoRelation;
	}

	public Collection<Condition<LETTER, PLACE>> getConditions() {
		return mConditions;
	}

	public Collection<Event<LETTER, PLACE>> getEvents() {
		return mEvents;
	}

	public Set<Condition<LETTER, PLACE>> getConditions(final PLACE p) {
		return Collections.unmodifiableSet(mPlace2Conds.getImage(p));
	}

	/**
	 * @return The initial conditions.
	 */
	public Collection<Condition<LETTER, PLACE>> initialConditions() {
		return mDummyRoot.getSuccessorConditions();
	}

	/**
	 * Returns all minimal events of this branching process with respect to the causal order. An event is causally
	 * minimal iff all its predecessors are initial conditions. Events with a non-initial preceding condition c cannot
	 * be minimal. Because c is non-initial it has to be preceded by another event which is causally smaller.
	 *
	 * @return The causally minimal events
	 */
	public Collection<Event<LETTER, PLACE>> minEvents() {
		final Set<Event<LETTER, PLACE>> eventsConnectedToInitConditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> initCondition : initialConditions()) {
			eventsConnectedToInitConditions.addAll(initCondition.getSuccessorEvents());
		}
		final Set<Event<LETTER, PLACE>> minEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> succEvent : eventsConnectedToInitConditions) {
			if (initialConditions().containsAll(succEvent.getPredecessorConditions())) {
				minEvents.add(succEvent);
			}
		}
		return minEvents;
	}

	/**
	 * Returns the net associated with this branching process.
	 *
	 * @return Net associated with this branching process
	 */
	public IPetriNetSuccessorProvider<LETTER, PLACE> getNet() {
		return mNet;
	}

	/**
	 * Check if the Conditions c1 and c2 are in causal relation. Conditions c1 and c2 are in causal relation if
	 * <ul>
	 * <li>c1 != c2 and c1 is ancestor of c2</li>
	 * <li>or c1 != c2 and c2 is ancestor of c1</li>
	 * </ul>
	 *
	 * @param c1
	 *            first condition
	 * @param c2
	 *            second condition
	 * @return {@code true} iff the conditions are in causal relation
	 */
	public boolean inCausalRelation(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c1Ancestors = ancestorNodes(c1);
		if (c1Ancestors.contains(c2)) {
			return true;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		return c2Ancestors.contains(c1);
	}

	/**
	 * Check if Condition and Event are in causal relation. This is the case if
	 * <ul>
	 * <li>the condition is an ancestor of the event</li>
	 * <li>or the event is ancestor of the condition.</li>
	 * </ul>
	 *
	 * @param condition
	 *            condition
	 * @param event
	 *            event
	 * @return {@code true} iff condition and event are in causal relation
	 */
	public boolean inCausalRelation(final Condition<LETTER, PLACE> condition, final Event<LETTER, PLACE> event) {
		final Set<Object> cAncestors = ancestorNodes(condition);
		if (cAncestors.contains(event)) {
			return true;
		}
		final Set<Object> eAncestors = ancestorNodes(event);
		return eAncestors.contains(condition);
	}

	/**
	 * Check if the Conditions c1 and c2 are in conflict. In a branching process Conditions c1 and c2 are in conflict
	 * iff c1 != c2 and there exist two paths leading to c1 and c2 which start at the same condition and diverge
	 * immediately and never converge again.
	 *
	 * @param c1
	 *            first condition
	 * @param c2
	 *            second condition
	 * @return {@code true} iff the conditions are in conflict
	 */
	public boolean inConflict(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		return conflictPathCheck(c1, c2, c2Ancestors);
	}

	/**
	 * @return if c1 != c2 and c2 is no ancestor of c1 the result is true iff there is a path from a condition in
	 *         c2Ancestors to c1 that does not contain other elements of c2Ancestors.
	 */
	private boolean conflictPathCheck(final Condition<LETTER, PLACE> c1In, final Condition<LETTER, PLACE> c2,
			final Set<Object> c2Ancestors) {
		final ArrayDeque<Condition<LETTER, PLACE>> worklist = new ArrayDeque<>();
		final Set<Condition<LETTER, PLACE>> done = new HashSet<>();
		worklist.add(c1In);

		while (!worklist.isEmpty()) {
			final Condition<LETTER, PLACE> c1 = worklist.pop();
			if (done.contains(c1)) {
				continue;
			}
			done.add(c1);

			if (c1 == c2) {
				throw new IllegalArgumentException(c1 + " ancestor of " + c2);
			}
			if (c2Ancestors.contains(c1)) {
				return true;
			}

			final Event<LETTER, PLACE> pred = c1.getPredecessorEvent();
			if (c2Ancestors.contains(pred) || pred == mDummyRoot) {
				continue;
			}

			worklist.addAll(pred.getPredecessorConditions());
		}
		return false;
	}

	/**
	 * @return Set containing all Conditions and Events which are (strict) ancestors of a Condition. The dummyRoot is
	 *         not considered as an ancestor.
	 */
	private Set<Object> ancestorNodes(final Condition<LETTER, PLACE> condition) {
		final Event<LETTER, PLACE> pred = condition.getPredecessorEvent();
		if (pred.equals(mDummyRoot)) {
			return Collections.emptySet();
		}
		return ancestorNodes(pred);
	}

	/**
	 * @return Set containing all Conditions and Events which are ancestors of an Event. The dummyRoot is not considered
	 *         as an ancestor.
	 */
	private Set<Object> ancestorNodes(final Event<LETTER, PLACE> event) {
		final Set<Object> ancestorConditionAndEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> e : event.getLocalConfiguration()) {
			ancestorConditionAndEvents.add(e);
			ancestorConditionAndEvents.addAll(e.getPredecessorConditions());
		}
		return ancestorConditionAndEvents;
	}

	/**
	 * @param conditions
	 *            The conditions.
	 * @return {@code true} iff all elements are pairwise in conflict or in co-relation
	 */
	public boolean pairwiseConflictOrCausalRelation(final Collection<Condition<LETTER, PLACE>> conditions) {
		if (conditions.isEmpty()) {
			throw new IllegalArgumentException("method only defined for non-empty set of conditions");
		}
		boolean result = true;
		for (final Condition<LETTER, PLACE> c1 : conditions) {
			for (final Condition<LETTER, PLACE> c2 : conditions) {
				if (!inCausalRelation(c1, c2) && !inConflict(c1, c2)) {
					result = false;
				}
			}
		}
		return result;
	}

	public boolean getNewFiniteComprehensivePrefixMode() {
		return mNewFiniteComprehensivePrefixMode;
	}

	/**
	 * #Backfolding
	 *
	 * @param cond
	 *            : a condition
	 * @return the set of Co
	 */
	public Set<PLACE> computeCoRelatedPlaces(final Condition<LETTER, PLACE> cond) {
		final Set<PLACE> result = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : mCoRelation.computeCoRelatatedConditions(cond)) {
			result.add(c.getPlace());
		}
		return result;
	}

	/**
	 * We call a transition "vital" if there is an accepting firing sequence in which this transition occurs.
	 * <p>
	 * 20200216 Matthias: Warning! Currently, this method computes only a superset of the vital transitions.
	 * </p>
	 */
	public Set<Transition<LETTER, PLACE>> computeVitalTransitions() {
		final HashRelation<Event<LETTER, PLACE>, Event<LETTER, PLACE>> companion2cutoff = new HashRelation<>();
		for (final Event<LETTER, PLACE> e : getEvents()) {
			if (e.isCutoffEvent()) {
				companion2cutoff.addPair(e.getCompanion(), e);
			}
		}
		final Set<Condition<LETTER, PLACE>> acceptingConditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : getConditions()) {
			if (mNet.isAccepting(c.getPlace())) {
				acceptingConditions.add(c);
			}
		}
		final Set<Event<LETTER, PLACE>> vitalEvents = new HashSet<>();
		final ArrayDeque<Event<LETTER, PLACE>> worklist = new ArrayDeque<>();
		for (final Condition<LETTER, PLACE> c : acceptingConditions) {
			final Event<LETTER, PLACE> pred = c.getPredecessorEvent();
			if (!vitalEvents.contains(pred)) {
				vitalEvents.add(pred);
				worklist.add(pred);
			}
		}
		computeAncestors(companion2cutoff, vitalEvents, worklist);
		for (final Condition<LETTER, PLACE> c : acceptingConditions) {
			for (final Event<LETTER, PLACE> coRelated : mCoRelation.computeCoRelatatedEvents(c)) {
				if (!vitalEvents.contains(coRelated)) {
					vitalEvents.add(coRelated);
					worklist.add(coRelated);
				}
			}
		}
		computeAncestors(companion2cutoff, vitalEvents, worklist);
		final Set<Transition<LETTER, PLACE>> vitalTransitions =
				vitalEvents.stream().filter(x -> x != mDummyRoot).map(Event::getTransition).collect(Collectors.toSet());
		return vitalTransitions;
	}

	private void computeAncestors(final HashRelation<Event<LETTER, PLACE>, Event<LETTER, PLACE>> companion2cutoff,
			final Set<Event<LETTER, PLACE>> vitalEvents, final ArrayDeque<Event<LETTER, PLACE>> worklist) {
		while (!worklist.isEmpty()) {
			final Event<LETTER, PLACE> e = worklist.remove();
			for (final Condition<LETTER, PLACE> c : e.getPredecessorConditions()) {
				final Event<LETTER, PLACE> pred = c.getPredecessorEvent();
				if (!vitalEvents.contains(pred)) {
					vitalEvents.add(pred);
					worklist.add(pred);
				}
			}
			for (final Event<LETTER, PLACE> eCutoff : companion2cutoff.getImage(e)) {
				if (!vitalEvents.contains(eCutoff)) {
					vitalEvents.add(eCutoff);
					worklist.add(eCutoff);
				}
				// 20200216 Matthias: Workaround proposed by Mehdi that makes
				// sure that we compute an overapproximation of the vital
				// events. Idea: While jumping from a companion e' back to a
				// cut-off event e, we loose the information which
				// backward-reachable condition set that contains e' successors
				// corresponds to which condition set that contains e
				// successors. We add all co-related events of e to make sure
				// that we do not miss a vital event and accept that we add
				// non-vital events to the output.
				for (final Event<LETTER, PLACE> eCorel : mCoRelation.computeCoRelatatedEvents(eCutoff)) {
					if (!vitalEvents.contains(eCorel)) {
						vitalEvents.add(eCorel);
						worklist.add(eCorel);
					}
				}
			}
		}
	}

	/**
	 * Compute all cuts (maximal co-sets) of the Branching Process
	 *
	 * @return List of all cuts
	 */
	public List<ImmutableList<Condition<LETTER, PLACE>>> computeCuts() {
		final var corelation = getCoRelation();

		final Condition<LETTER, PLACE>[] conditions = getConditions().toArray(Condition[]::new);
		final var cosets = new ArrayList<ImmutableList<Condition<LETTER, PLACE>>>();
		final var worklist = new ArrayDeque<Pair<ImmutableList<Condition<LETTER, PLACE>>, Integer>>();
		worklist.add(new Pair<>(ImmutableList.empty(), 0));

		while (!worklist.isEmpty()) {
			final var pair = worklist.pop();
			final var coset = pair.getFirst();
			final int minIndex = pair.getSecond();
			boolean isMaximal = true;

			ImmutableList<Condition<LETTER, PLACE>> extendedCoset = null;

			for (int i = minIndex; i < conditions.length; ++i) {
				final Condition<LETTER, PLACE> candidate = conditions[i];
				final boolean acceptCandidate = corelation.isCoset(coset, candidate);
				if (acceptCandidate) {
					if (extendedCoset != null) {
						worklist.push(new Pair<>(extendedCoset, i));
					}

					isMaximal = false;
					extendedCoset = new ImmutableList<>(candidate, coset);
				}
			}
			if (extendedCoset != null) {
				worklist.push(new Pair<>(extendedCoset, conditions.length));
			}

			for (int i = 0; isMaximal && i < minIndex; ++i) {
				isMaximal &= coset.contains(conditions[i]) || !corelation.isCoset(coset, conditions[i]);
			}

			if (isMaximal) {
				cosets.add(coset);
			}
		}

		return cosets;
	}

	@Override
	public String sizeInformation() {
		// Subtract one from size of events because of auxiliary/dummy initial event.
		return "has " + mConditions.size() + " conditions, " + (mEvents.size() - 1) + " events";
	}

	public ConfigurationOrder<LETTER, PLACE> getOrder() {
		return mOrder;
	}

	@Override
	public int size() {
		return mConditions.size();
	}

	public int computeConditionPerPlaceMax() {
		final int max = mPlace2Conds.getDomain().stream().map(x -> mPlace2Conds.getImage(x).size())
				.max(Integer::compare).orElse(0);
		return max;
	}

	public HashRelation<PLACE, Transition<LETTER, PLACE>> getYetKnownPredecessorTransitions() {
		return mYetKnownPredecessorTransitions;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mNet.getAlphabet();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new BranchingProcessToUltimateModel<LETTER, PLACE>().transformToUltimateModel(this);
	}

	@Override
	public String toString() {
		return (AutomatonDefinitionPrinter.toString(mServices, "branchingProcess", this));
	}

	public Collection<Condition<LETTER, PLACE>> getAcceptingConditions() {
		return mConditions.stream().filter(c -> mNet.isAccepting(c.getPlace())).collect(Collectors.toSet());
	}
}
