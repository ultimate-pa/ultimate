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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IFinitePrefix2PetriNetStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Converts to Petri net.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <L>
 *            letter type
 * @param <PLACE>
 *            content type
 */
public final class FinitePrefix2PetriNet<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {
	private final BranchingProcess<LETTER, PLACE> mInput;
	private final BoundedPetriNet<LETTER, PLACE> mNet;
	private final UnionFind<Condition<LETTER, PLACE>> mRepresentatives;
	private final IFinitePrefix2PetriNetStateFactory<PLACE> mStateFactory;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 * @param bp
	 *            branching process
	 * @param net2autoStateFactory
	 * @param nwaInclusionStateFactory
	 * @throws AutomataLibraryException
	 *             if two nets do not have the same alphabet.
	 */
	public FinitePrefix2PetriNet(final AutomataLibraryServices services,
			final IFinitePrefix2PetriNetStateFactory<PLACE> stateFactory, final BranchingProcess<LETTER, PLACE> bp) throws AutomataLibraryException {
		super(services);
		mStateFactory = stateFactory;
		final IPetriNet2FiniteAutomatonStateFactory<PLACE> net2autoStateFactory = (IPetriNet2FiniteAutomatonStateFactory<PLACE>) stateFactory;
		final INwaInclusionStateFactory<PLACE> nwaInclusionStateFactory = (INwaInclusionStateFactory<PLACE>) stateFactory;
		// TODO implement merging for markings?
		mInput = bp;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final BoundedPetriNet<LETTER, PLACE> oldNet = mInput.getNet();
		mNet = new BoundedPetriNet<>(mServices, oldNet.getAlphabet(), false);
		mRepresentatives = new UnionFind<>();
		constructNet(bp, oldNet);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
		assert petriNetLanguageEquivalence(oldNet, mNet, net2autoStateFactory, nwaInclusionStateFactory) : "The language recognized by the FinitePrefix2PetriNet is "
				+ "not equal to the language of the original net.";
	}

	@SuppressWarnings("squid:S1698")
	private void constructNet(final BranchingProcess<LETTER, PLACE> bp, final BoundedPetriNet<LETTER, PLACE> oldNet) {
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

		/*
		final List<Event<LETTER, PLACE>> events = new ArrayList<>();
		final List<Event<LETTER, PLACE>> worklist = new LinkedList<Event<LETTER, PLACE>>();
		final Set<Event<LETTER, PLACE>> visited = new HashSet<>();

		for (final Event<LETTER, PLACE> e : bp.getMinEvents()) {
			worklist.add(e);
			events.add(e);
			visited.add(e);
		}
		while (!worklist.isEmpty()) {
			final Event<LETTER, PLACE> event = worklist.remove(0);
			for (final Condition<LETTER, PLACE> c : event.getSuccessorConditions()) {
				for (final Event<LETTER, PLACE> e : c.getSuccessorEvents()) {
					if (!visited.contains(e)) {
						worklist.add(e);
						events.add(e);
						visited.add(e);
					}
				}
			}
		}
		for (final Event e : bp.getEvents()) {
			assert e == bp.getDummyRoot() || visited.contains(e);
		}
		*/

		final TreeSet<Event<LETTER, PLACE>> events = new TreeSet<>(bp.getOrder());
		events.addAll(bp.getEvents());

		for (final Condition<LETTER, PLACE> c : bp.getDummyRoot().getSuccessorConditions()) {
			mRepresentatives.makeEquivalenceClass(c);
		}
		final Iterator<Event<LETTER, PLACE>> it = events.iterator();
		final Event<LETTER, PLACE> first = it.next();
		// equality intended here
		assert first == bp.getDummyRoot();
		Event<LETTER, PLACE> previous;
		Event<LETTER, PLACE> current = first;
		while (it.hasNext()) {
			previous = current;
			current = it.next();
			assert bp.getOrder().compare(previous, current) < 0;

			for (final Condition<LETTER, PLACE> c : current.getConditionMark()) {
				final Condition<LETTER, PLACE> representative = mRepresentatives.find(c);
				if (representative == null) {
					mRepresentatives.makeEquivalenceClass(c);
				}
			}

			if (current.isCutoffEvent()) {
				final Event<LETTER, PLACE> companion = current.getCompanion();
				final ConditionMarking<LETTER, PLACE> companionCondMark = companion.getConditionMark();
				final ConditionMarking<LETTER, PLACE> eCondMark = current.getConditionMark();
				mergeConditions(companionCondMark, eCondMark);
				mergeConditions(companion.getPredecessorConditions(), current.getPredecessorConditions());
			}

		}

		final Map<Condition<LETTER, PLACE>, PLACE> placeMap = new HashMap<>();
		for (final Condition<LETTER, PLACE> c : bp.getConditions()) {
			assert mRepresentatives.find(c) != null;
			// equality intended here
			if (c == mRepresentatives.find(c)) {
				final PLACE place = mNet.addPlace(mStateFactory.finitePrefix2net(c),
						bp.initialConditions().contains(c), bp.isAccepting(c));
				placeMap.put(c, place);
			}
		}
		final TransitionSet transitionSet = new TransitionSet();
		for (final Event<LETTER, PLACE> e : events) {
			// equality intended here
			if (e == bp.getDummyRoot()) {
				continue;
			}
			final Set<PLACE> preds = new HashSet<>();
			final Set<PLACE> succs = new HashSet<>();

			for (final Condition<LETTER, PLACE> c : e.getPredecessorConditions()) {
				final Condition<LETTER, PLACE> representative = mRepresentatives.find(c);
				preds.add(placeMap.get(representative));
			}

			for (final Condition<LETTER, PLACE> c : e.getSuccessorConditions()) {
				final Condition<LETTER, PLACE> representative = mRepresentatives.find(c);
				succs.add(placeMap.get(representative));
			}
			transitionSet.addTransition(e.getTransition().getSymbol(), preds, succs);
			// mNet.addTransition(e.getTransition().getSymbol(), preds, succs);
		}
		transitionSet.addAllTransitionsToNet(mNet);

		/*
		for (final Condition<LETTER, PLACE> c : bp.getConditions()) {
			if (!c.getPredecessorEvent().isCutoffEvent()) {
				final PLACE place = mNet.addPlace(old_net.getStateFactory()
						.finitePrefix2net(c), bp.initialConditions()
								.contains(c),
						bp.isAccepting(c));
				placeMap.put(c, place);
			}
		}
		mLogger.debug("CONDITIONS TO PLACE:");
		for (final Map.Entry<Condition<LETTER, PLACE>, C> en : placeMap.entrySet()) {
			mLogger.debug(en);
		}
		for (final Event<LETTER, PLACE> e : bp.getEvents()) {
			if (e.getTransition() == null) {
				continue;
			}
			final ArrayList<PLACE> preds = new ArrayList<>();
			final ArrayList<PLACE> succs = new ArrayList<>();
			for (final Condition<LETTER, PLACE> pc : e.getPredecessorConditions()) {
				assert placeMap.containsKey(pc) : pc.toString()
						+ " has successors, hence cannot be child of cut-off event." +
						" So it must have been added, but it cannot be found.";
				preds.add(placeMap.get(pc));
			}
			Event<LETTER, PLACE> companionOrE = e;
			if (e.isCutoffEvent()) {
				companionOrE = e.getCompanion();
			}
			for (final Condition<LETTER, PLACE> sc : companionOrE.getSuccessorConditions()) {
				assert placeMap.containsKey(sc);
				succs.add(placeMap.get(sc));
			}
			final Transition<LETTER, PLACE> transition = mNet.addTransition(e.getTransition()
					.getSymbol(), preds, succs);
			transitionMap.put(e, transition);
		}
		*/
	}

	private boolean petriNetLanguageEquivalence(final BoundedPetriNet<LETTER, PLACE> oldNet, final BoundedPetriNet<LETTER, PLACE> newNet,
			final IPetriNet2FiniteAutomatonStateFactory<PLACE> net2autoStateFactory,
			final INwaInclusionStateFactory<PLACE> nwaInclusionStateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing Petri net language equivalence");
		}

		final INestedWordAutomaton<LETTER, PLACE> finAuto1 = (new PetriNet2FiniteAutomaton<>(mServices, net2autoStateFactory, oldNet))
				.getResult();
		final INestedWordAutomaton<LETTER, PLACE> finAuto2 = (new PetriNet2FiniteAutomaton<>(mServices, net2autoStateFactory, newNet))
				.getResult();
		final NestedRun<LETTER, PLACE> subsetCounterex = new IsIncluded<>(mServices, nwaInclusionStateFactory, finAuto1,
				finAuto2).getCounterexample();
		final boolean subset = subsetCounterex == null;
		if (!subset && mLogger.isErrorEnabled()) {
			mLogger.error("Only accepted by first: " + subsetCounterex.getWord());
		}
		final NestedRun<LETTER, PLACE> supersetCounterex = new IsIncluded<>(mServices, nwaInclusionStateFactory, finAuto2,
				finAuto1).getCounterexample();
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
		return "Finished " + getOperationName() + ". Result " + mNet.sizeInformation();
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mNet;
	}

	/*
	private Condition<LETTER, PLACE> getRepresentative(final Condition<LETTER, PLACE> c) {
		Condition<LETTER, PLACE> result = c;
		while (result != representatives.get(result)) {
			result = representatives.get(result);
			assert result != null;
		}
		return result;
	}
	*/

	private void mergeConditions(final Iterable<Condition<LETTER, PLACE>> set1, final Iterable<Condition<LETTER, PLACE>> set2) {
		final Map<PLACE, Condition<LETTER, PLACE>> origPlace2Condition = new HashMap<>();
		for (final Condition<LETTER, PLACE> cond1 : set1) {
			origPlace2Condition.put(cond1.getPlace(), cond1);
		}

		for (final Condition<LETTER, PLACE> cond2 : set2) {
			final PLACE p2 = cond2.getPlace();
			assert p2 != null : "no condition for place " + p2;
			final Condition<LETTER, PLACE> c1 = origPlace2Condition.get(p2);
			final Condition<LETTER, PLACE> c1representative = mRepresentatives.find(c1);
			assert c1representative != null;

			final Condition<LETTER, PLACE> c2representative = mRepresentatives.find(cond2);
			assert c2representative != null;

			mRepresentatives.union(c1representative, c2representative);
		}
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
			for (final Entry<LETTER, Map<Set<PLACE>, Set<Set<PLACE>>>> entry1 : mLetter2Predset2Succsets
					.entrySet()) {
				final LETTER letter = entry1.getKey();
				final Map<Set<PLACE>, Set<Set<PLACE>>> predsets2succsets = entry1.getValue();
				for (final Entry<Set<PLACE>, Set<Set<PLACE>>> entry2 : predsets2succsets.entrySet()) {
					final Set<PLACE> predset = entry2.getKey();
					final Set<Set<PLACE>> succsets = entry2.getValue();
					for (final Set<PLACE> succset : succsets) {
						final Set<PLACE> predList = new HashSet<>(predset);
						final Set<PLACE> succList = new HashSet<>(succset);
						net.addTransition(letter, predList, succList);
					}
				}
			}
		}
	}
}
