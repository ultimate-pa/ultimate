/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IFinitePrefix2PetriNetStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Converts to Petri net.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <L>
 *            letter type
 * @param <PLACE>
 *            content type
 */
public final class FinitePrefix2PetriNet<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNetAndAutomataInclusionStateFactory<PLACE>> {
	private final BranchingProcess<LETTER, PLACE> mInput;
	private final BoundedPetriNet<LETTER, PLACE> mNet;
	private final HashDeque<Pair<Event<LETTER, PLACE>, Event<LETTER, PLACE>>> mMergingCandidates;
	private final HashRelation<Event<LETTER, PLACE>, Condition<LETTER, PLACE>> mConditionPredecessors =
			new HashRelation<>();
	private final HashRelation<Condition<LETTER, PLACE>, Event<LETTER, PLACE>> mEventSuccessors = new HashRelation<>();
	private final UnionFind<Condition<LETTER, PLACE>> mConditionRepresentatives;
	private final UnionFind<Event<LETTER, PLACE>> mEventRepresentatives;
	private final IFinitePrefix2PetriNetStateFactory<PLACE> mStateFactory;
	private final HashRelation<PLACE, PLACE> mOldToNewPlaces = new HashRelation<>();
	private final HashRelation<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mOldToNewTransitions =
			new HashRelation<>();
	private final boolean mUsePetrification = false;
	private final boolean mRemoveDeadTransitions;
	private int mNumberOfCallsOfMergeCondidates = 0;
	private int mNumberOfMergingCondidates = 0;
	private int mNumberOfMergedEventPairs = 0;
	private int mNumberOfAddOperationsToTheCandQueue = 0;
	private final Set<Event<LETTER, PLACE>> mVitalRepresentatives = new HashSet<>();

	public FinitePrefix2PetriNet(final AutomataLibraryServices services,
			final IFinitePrefix2PetriNetStateFactory<PLACE> stateFactory, final BranchingProcess<LETTER, PLACE> bp) {
		this(services, stateFactory, bp, false);
	}

	public FinitePrefix2PetriNet(final AutomataLibraryServices services,
			final IFinitePrefix2PetriNetStateFactory<PLACE> stateFactory, final BranchingProcess<LETTER, PLACE> bp,
			final boolean removeDeadTransitions) {
		super(services);
		mStateFactory = stateFactory;
		// TODO implement merging for markings?
		mInput = bp;
		mRemoveDeadTransitions = removeDeadTransitions;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final BoundedPetriNet<LETTER, PLACE> oldNet = (BoundedPetriNet<LETTER, PLACE>) mInput.getNet();
		if (mUsePetrification) {
			mNet = buildPetrification(bp);
			mMergingCandidates = null;
			mConditionRepresentatives = null;
			mEventRepresentatives = null;
		} else {
			mMergingCandidates = new HashDeque<>();
			mNet = new BoundedPetriNet<>(mServices, oldNet.getAlphabet(), false);
			mConditionRepresentatives = new UnionFind<>();
			mEventRepresentatives = new UnionFind<>();
			constructNet(bp);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private void constructNet(final BranchingProcess<LETTER, PLACE> bp) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("CONDITIONS:");
			for (final Condition<LETTER, PLACE> c : bp.getConditions()) {
				mLogger.debug(c);
			}
			mLogger.debug("EVENTS:");
			for (final Event<LETTER, PLACE> e : bp.getEvents()) {
				mLogger.debug(e.getPredecessorConditions() + " || " + e + " || " + e.getSuccessorConditions());
			}
		}

		for (final Event<LETTER, PLACE> e : bp.getEvents()) {
			mEventRepresentatives.makeEquivalenceClass(e);
			for (final Condition<LETTER, PLACE> c : e.getSuccessorConditions()) {
				assert mConditionRepresentatives.find(c) == null;
				mConditionRepresentatives.makeEquivalenceClass(c);
			}
			for (final Condition<LETTER, PLACE> c : e.getPredecessorConditions()) {
				mEventSuccessors.addPair(c, e);
			}
			mConditionPredecessors.addAllPairs(e, e.getPredecessorConditions());
		}

		// equality intended here
		for (final Event<LETTER, PLACE> e : bp.getEvents()) {
			if (e.isCutoffEvent()) {
				final Event<LETTER, PLACE> companion = e.getCompanion();
				final ConditionMarking<LETTER, PLACE> companionCondMark = companion.getConditionMark();
				final ConditionMarking<LETTER, PLACE> eCondMark = e.getConditionMark();
				mergeConditions(eCondMark.getConditions(), companionCondMark.getConditions());
				while (!mMergingCandidates.isEmpty()) {
					mNumberOfMergingCondidates++;
					final Pair<Event<LETTER, PLACE>, Event<LETTER, PLACE>> candidate = mMergingCandidates.poll();
					final Event<LETTER, PLACE> e1 = mEventRepresentatives.find(candidate.getFirst());
					final Event<LETTER, PLACE> e2 = mEventRepresentatives.find(candidate.getSecond());
					if (!e1.equals(e2)
							&& mConditionPredecessors.getImage(e1).equals(mConditionPredecessors.getImage(e2))) {
						mEventRepresentatives.union(e1, e2);
						final Event<LETTER, PLACE> rep = mEventRepresentatives.find(e1);
						final Event<LETTER, PLACE> nonRep;
						if (rep.equals(e1)) {
							nonRep = e2;
						} else {
							nonRep = e1;
						}
						for (final Condition<LETTER, PLACE> c : mConditionPredecessors.getImage(nonRep)) {
							mEventSuccessors.removePair(c, nonRep);
							mEventSuccessors.addPair(c, rep);
						}
						mConditionPredecessors.addAllPairs(rep, mConditionPredecessors.getImage(nonRep));
						mConditionPredecessors.removeDomainElement(nonRep);
						mNumberOfMergedEventPairs++;
						mergeConditions(e1.getSuccessorConditions(), e2.getSuccessorConditions());
					}
				}
			}

		}
		final Set<Event<LETTER, PLACE>> releventEvents = new HashSet<>(mEventRepresentatives.getAllRepresentatives());
		releventEvents.remove(mInput.getDummyRoot());

		if (mRemoveDeadTransitions) {
			final HashRelation<Event<LETTER, PLACE>, Event<LETTER, PLACE>> companion2cutoff = new HashRelation<>();
			for (final Event<LETTER, PLACE> e : bp.getEvents()) {
				if (e.isCutoffEvent()) {
					companion2cutoff.addPair(e.getCompanion(), e);
				}
			}
			final ArrayDeque<Event<LETTER, PLACE>> worklist = new ArrayDeque<>();
			// TODO: Try if the condition representatives are sufficient
			for (final Condition<LETTER, PLACE> c : bp.getAcceptingConditions()) {
				final Event<LETTER, PLACE> predRepresentative = mEventRepresentatives.find(c.getPredecessorEvent());
				if (mVitalRepresentatives.add(predRepresentative)) {
					worklist.add(predRepresentative);
				}
				for (final Event<LETTER, PLACE> e : bp.getCoRelation().computeCoRelatatedEvents(c)) {
					if (mVitalRepresentatives.add(mEventRepresentatives.find(e))) {
						worklist.add(mEventRepresentatives.find(e));
					}
				}
			}
			while (!worklist.isEmpty()) {
				final Event<LETTER, PLACE> representative = worklist.removeFirst();
				for (final Event<LETTER, PLACE> e : mEventRepresentatives.getEquivalenceClassMembers(representative)) {
					for (final Event<LETTER, PLACE> predEvent : e.getPredecessorEvents()) {
						final Event<LETTER, PLACE> predEventRep = mEventRepresentatives.find(predEvent);
						if (mVitalRepresentatives.add(predEventRep)) {
							worklist.add(predEventRep);
						}
					}
					for (final Event<LETTER, PLACE> cutoffEvent : companion2cutoff.getImage(e)) {
						final Event<LETTER, PLACE> cutoffEventRep = mEventRepresentatives.find(cutoffEvent);
						if (mVitalRepresentatives.add(cutoffEventRep)) {
							worklist.add(cutoffEventRep);
						}
					}
				}
			}
			mVitalRepresentatives.remove(bp.getDummyRoot());
			releventEvents.retainAll(mVitalRepresentatives);
		}
		final Map<Condition<LETTER, PLACE>, PLACE> placeMap = new HashMap<>();
		for (final Condition<LETTER, PLACE> c : mConditionRepresentatives.getAllRepresentatives()) {
			final boolean isInitial =
					containsInitial(mConditionRepresentatives.getEquivalenceClassMembers(c), bp.initialConditions());
			final boolean isAccepting = bp.getNet().isAccepting(c.getPlace());
			final PLACE place = mStateFactory.finitePrefix2net(c);
			mOldToNewPlaces.addPair(c.getPlace(), place);
			final boolean newlyAdded = mNet.addPlace(place, isInitial, isAccepting);
			if (!newlyAdded) {
				throw new AssertionError("Must not add place twice: " + place);
			}
			placeMap.put(c, place);
		}
		for (final Event<LETTER, PLACE> e : releventEvents) {
			final Set<PLACE> preds = new HashSet<>();
			final Set<PLACE> succs = new HashSet<>();

			for (final Condition<LETTER, PLACE> c : e.getPredecessorConditions()) {
				final Condition<LETTER, PLACE> representative = mConditionRepresentatives.find(c);
				preds.add(placeMap.get(representative));
			}
			for (final Condition<LETTER, PLACE> c : e.getSuccessorConditions()) {
				final Condition<LETTER, PLACE> representative = mConditionRepresentatives.find(c);
				succs.add(placeMap.get(representative));
			}
			final Transition<LETTER, PLACE> newTransition =
					mNet.addTransition(e.getTransition().getSymbol(), ImmutableSet.of(preds), ImmutableSet.of(succs));
			mOldToNewTransitions.addPair(newTransition, e.getTransition());
		}
	}

	public Set<Transition<LETTER, PLACE>> computeVitalTransitions() {
		assert mRemoveDeadTransitions : "remove dead transitions must be enabled";
		return mVitalRepresentatives.stream().map(Event::getTransition).collect(Collectors.toSet());
	}

	private boolean containsInitial(final Set<Condition<LETTER, PLACE>> equivalenceClassMembers,
			final Collection<Condition<LETTER, PLACE>> initialConditions) {
		return initialConditions.stream().anyMatch(x -> equivalenceClassMembers.contains(x));
	}

	private boolean petriNetLanguageEquivalence(final BoundedPetriNet<LETTER, PLACE> oldNet,
			final BoundedPetriNet<LETTER, PLACE> newNet,
			final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing Petri net language equivalence");
		}

		final INestedWordAutomaton<LETTER, PLACE> finAuto1 =
				new PetriNet2FiniteAutomaton<>(mServices, stateFactory, oldNet).getResult();
		final INestedWordAutomaton<LETTER, PLACE> finAuto2 =
				new PetriNet2FiniteAutomaton<>(mServices, stateFactory, newNet).getResult();
		final NestedRun<LETTER, PLACE> subsetCounterex =
				new IsIncluded<>(mServices, stateFactory, finAuto1, finAuto2).getCounterexample();
		final boolean subset = subsetCounterex == null;
		if (!subset && mLogger.isErrorEnabled()) {
			mLogger.error("Only accepted by first: " + subsetCounterex.getWord());
		}
		final NestedRun<LETTER, PLACE> supersetCounterex =
				new IsIncluded<>(mServices, stateFactory, finAuto2, finAuto1).getCounterexample();
		final boolean superset = supersetCounterex == null;
		if (!superset && mLogger.isErrorEnabled()) {
			mLogger.error("Only accepted by second: " + supersetCounterex.getWord());
		}
		final boolean result = subset && superset;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished Petri net language equivalence");
		}
		return result;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Input " + mInput.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mNet.sizeInformation() + ". Original net "
				+ mInput.getNet().sizeInformation() + ".";
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mNet;
	}

	private void mergeConditions(final Set<Condition<LETTER, PLACE>> set1, final Set<Condition<LETTER, PLACE>> set2) {
		mNumberOfCallsOfMergeCondidates++;
		final Map<PLACE, Condition<LETTER, PLACE>> origPlace2Condition = new HashMap<>();
		final Set<Condition<LETTER, PLACE>> s2 =
				set2.stream().map(x -> mConditionRepresentatives.find(x)).collect(Collectors.toSet());
		for (final Condition<LETTER, PLACE> c1 : set1) {
			final Condition<LETTER, PLACE> c1representative = mConditionRepresentatives.find(c1);
			if (!s2.remove(c1representative)) {
				origPlace2Condition.put(c1.getPlace(), c1representative);
			}
		}
		for (final Condition<LETTER, PLACE> c2 : s2) {
			final PLACE p2 = c2.getPlace();
			assert p2 != null : "no place for condition " + c2;
			final Condition<LETTER, PLACE> c1 = origPlace2Condition.get(p2);
			assert c1 != null : "no condition for place " + p2;
			for (final Event<LETTER, PLACE> e1 : mEventSuccessors.getImage(c1)) {
				for (final Event<LETTER, PLACE> e2 : mEventSuccessors.getImage(c2)) {
					if (e1.getTransition().equals(e2.getTransition())) {
						mMergingCandidates
								.add(new Pair<>(mEventRepresentatives.find(e1), mEventRepresentatives.find(e2)));
						mNumberOfAddOperationsToTheCandQueue++;
					}
				}

			}
			mConditionRepresentatives.union(c1, c2);
			final Condition<LETTER, PLACE> rep = mConditionRepresentatives.find(c1);
			final Condition<LETTER, PLACE> nonRep;
			if (rep.equals(c1)) {
				nonRep = c2;
			} else {
				nonRep = c1;
			}

			for (final Event<LETTER, PLACE> e : mEventSuccessors.getImage(nonRep)) {
				mConditionPredecessors.removePair(e, nonRep);
				mConditionPredecessors.addPair(e, rep);
			}
			mEventSuccessors.addAllPairs(rep, mEventSuccessors.getImage(nonRep));
			mEventSuccessors.removeDomainElement(nonRep);
		}
	}

	public HashRelation<PLACE, PLACE> getOldToNewPlaces() {
		return mOldToNewPlaces;
	}

	public HashRelation<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> getOldToNewTransitions() {
		return mOldToNewTransitions;
	}

	/**
	 * A transition set.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	class TransitionSet {
		private final Map<LETTER, Map<Set<PLACE>, Set<Set<PLACE>>>> mLetter2Predset2Succsets = new HashMap<>();

		void addTransition(final LETTER letter, final Set<PLACE> predset, final Set<PLACE> succset) {
			Map<Set<PLACE>, Set<Set<PLACE>>> predsets2succsets = mLetter2Predset2Succsets.get(letter);
			if (predsets2succsets == null) {
				predsets2succsets = new HashMap<>();
				mLetter2Predset2Succsets.put(letter, predsets2succsets);
			}
			Set<Set<PLACE>> succsets = predsets2succsets.get(predset);
			if (succsets == null) {
				succsets = new HashSet<>();
				predsets2succsets.put(predset, succsets);
			}
			succsets.add(succset);
		}

		void addAllTransitionsToNet(final BoundedPetriNet<LETTER, PLACE> net) {
			for (final Entry<LETTER, Map<Set<PLACE>, Set<Set<PLACE>>>> entry1 : mLetter2Predset2Succsets.entrySet()) {
				final LETTER letter = entry1.getKey();
				final Map<Set<PLACE>, Set<Set<PLACE>>> predsets2succsets = entry1.getValue();
				for (final Entry<Set<PLACE>, Set<Set<PLACE>>> entry2 : predsets2succsets.entrySet()) {
					final Set<PLACE> predset = entry2.getKey();
					final Set<Set<PLACE>> succsets = entry2.getValue();
					for (final Set<PLACE> succset : succsets) {
						net.addTransition(letter, ImmutableSet.copyOf(predset), ImmutableSet.copyOf(succset));
					}
				}
			}
		}
	}

	/**
	 * @return false iff there exists transition t such that c1 and c2 both have an outgoing event that is labeled with
	 *         t.
	 */
	private static <LETTER, PLACE> boolean areIndependent(final Condition<LETTER, PLACE> c1,
			final Condition<LETTER, PLACE> c2) {
		final Set<Transition<LETTER, PLACE>> c1SuccTrans =
				c1.getSuccessorEvents().stream().map(Event::getTransition).collect(Collectors.toSet());
		final Set<Transition<LETTER, PLACE>> c2SuccTrans =
				c2.getSuccessorEvents().stream().map(Event::getTransition).collect(Collectors.toSet());
		return Collections.disjoint(c1SuccTrans, c2SuccTrans);
	}

	public LinkedHashSet<Condition<LETTER, PLACE>> collectRelevantEvents() {
		final LinkedHashSet<Condition<LETTER, PLACE>> conditions = new LinkedHashSet<>();
		for (final Event<LETTER, PLACE> e : mInput.getEvents()) {
			if (!e.isCutoffEvent()) {
				conditions.addAll(e.getSuccessorConditions());
			}
		}
		return conditions;
	}

	private Map<PLACE, UnionFind<Condition<LETTER, PLACE>>>
			computeEquivalenceClasses(final Collection<Condition<LETTER, PLACE>> conditions) {
		final Map<PLACE, UnionFind<Condition<LETTER, PLACE>>> result = new HashMap<>();
		for (final Condition<LETTER, PLACE> c : conditions) {
			final UnionFind<Condition<LETTER, PLACE>> uf = result.computeIfAbsent(c.getPlace(), x -> new UnionFind<>());
			final List<Condition<LETTER, PLACE>> mergeRequired = new ArrayList<>();
			for (final Set<Condition<LETTER, PLACE>> eqClass : uf.getAllEquivalenceClasses()) {
				for (final Condition<LETTER, PLACE> otherCond : eqClass) {
					final boolean areIndependent = areIndependent(c, otherCond);
					if (!areIndependent) {
						mergeRequired.add(otherCond);
						// no need to check others of this equivalence class, will be merged anyway
						continue;
					}
				}
			}
			uf.makeEquivalenceClass(c);
			for (final Condition<LETTER, PLACE> otherCond : mergeRequired) {
				uf.union(c, otherCond);
			}
		}
		return result;
	}

	private BoundedPetriNet<LETTER, PLACE> buildPetrification(final BranchingProcess<LETTER, PLACE> bp) {
		final LinkedHashSet<Condition<LETTER, PLACE>> relevantConditions = collectRelevantEvents();
		final Map<PLACE, UnionFind<Condition<LETTER, PLACE>>> equivalenceClasses =
				computeEquivalenceClasses(relevantConditions);
		final Map<Condition<LETTER, PLACE>, PLACE> condition2Place =
				computeCondition2Place(equivalenceClasses, mStateFactory);

		final BoundedPetriNet<LETTER, PLACE> result = new BoundedPetriNet<>(mServices, bp.getAlphabet(), false);

		for (final Entry<Condition<LETTER, PLACE>, PLACE> entry : condition2Place.entrySet()) {
			if (!result.getPlaces().contains(entry.getValue())) {
				final boolean isInitial = entry.getKey().getPredecessorEvent() == bp.getDummyRoot();
				final boolean isAccepting = bp.getNet().isAccepting(entry.getKey().getPlace());
				final boolean newlyAdded = result.addPlace(entry.getValue(), isInitial, isAccepting);
				if (!newlyAdded) {
					throw new AssertionError("Must not add place twice: " + entry.getValue());
				}
			}
		}
		computeTransitions(bp.getEvents(), condition2Place)
				.forEach(x -> result.addTransition(x.getFirst(), x.getSecond(), x.getThird()));
		return result;
	}

	private HashRelation3<LETTER, ImmutableSet<PLACE>, ImmutableSet<PLACE>> computeTransitions(
			final Collection<Event<LETTER, PLACE>> events, final Map<Condition<LETTER, PLACE>, PLACE> condition2Place) {
		final HashRelation3<LETTER, ImmutableSet<PLACE>, ImmutableSet<PLACE>> letterPredecessorsSuccessors =
				new HashRelation3<>();
		for (final Event<LETTER, PLACE> event : events) {
			// skip auxiliary initial event
			if (event.getTransition() != null) {
				final ImmutableSet<PLACE> predecessors = event.getPredecessorConditions().stream()
						.map(condition2Place::get).collect(ImmutableSet.collector());
				assert !predecessors.contains(null);
				final ImmutableSet<PLACE> successors;
				if (event.getCompanion() != null) {
					final Event<LETTER, PLACE> companion = event.getCompanion();
					if (companion.getTransition() != event.getTransition()) {
						throw new UnsupportedOperationException("finite prefix with same transition cut-off required");
					}
					successors = companion.getSuccessorConditions().stream().map(condition2Place::get)
							.collect(ImmutableSet.collector());
				} else {
					successors = event.getSuccessorConditions().stream().map(condition2Place::get)
							.collect(ImmutableSet.collector());
				}
				assert !successors.contains(null);
				letterPredecessorsSuccessors.addTriple(event.getTransition().getSymbol(), predecessors, successors);
			}
		}
		return letterPredecessorsSuccessors;
	}

	private Map<Condition<LETTER, PLACE>, PLACE> computeCondition2Place(
			final Map<PLACE, UnionFind<Condition<LETTER, PLACE>>> equivalenceClasses,
			final IFinitePrefix2PetriNetStateFactory<PLACE> stateFactory) {
		final Map<Condition<LETTER, PLACE>, PLACE> result = new HashMap<>();
		for (final Entry<PLACE, UnionFind<Condition<LETTER, PLACE>>> entry : equivalenceClasses.entrySet()) {
			for (final Condition<LETTER, PLACE> rep : entry.getValue().getAllRepresentatives()) {
				final PLACE resultPlace = stateFactory.finitePrefix2net(rep);
				for (final Condition<LETTER, PLACE> eqMember : entry.getValue().getEquivalenceClassMembers(rep)) {
					result.put(eqMember, resultPlace);
				}
			}
		}
		return result;
	}

	@Override
	public boolean checkResult(final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		if (!(mInput.getNet() instanceof BoundedPetriNet)) {
			throw new AssertionError("implement result checking for on-demand inputs");
		}
		final BoundedPetriNet<LETTER, PLACE> originalNet = (BoundedPetriNet<LETTER, PLACE>) mInput.getNet();
		final boolean languagesEquivalent = petriNetLanguageEquivalence(originalNet, mNet, stateFactory);
		if (!languagesEquivalent) {
			mLogger.error("The result of the " + FinitePrefix2PetriNet.class.getSimpleName()
					+ " recognizes a different language than the original net.");
		}
		return languagesEquivalent;
	}

}
