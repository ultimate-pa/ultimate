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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
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
 * @param <C>
 *            content type
 */
public final class FinitePrefix2PetriNet<L, C> extends GeneralOperation<L, C, IStateFactory<C>> {
	private final BranchingProcess<L, C> mInput;
	private final BoundedPetriNet<L, C> mNet;
	private final UnionFind<Condition<L, C>> mRepresentatives;
	private final IFinitePrefix2PetriNetStateFactory<C> mStateFactory;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory 
	 * @param bp
	 *            branching process
	 * @throws AutomataLibraryException
	 *             if two nets do not have the same alphabet.
	 */
	public FinitePrefix2PetriNet(final AutomataLibraryServices services, IFinitePrefix2PetriNetStateFactory<C> stateFactory, final BranchingProcess<L, C> bp)
			throws AutomataLibraryException {
		super(services);
		mStateFactory = stateFactory;
		// TODO implement merging for markings?
		mInput = bp;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final BoundedPetriNet<L, C> oldNet = mInput.getNet();
		mNet = new BoundedPetriNet<>(mServices, oldNet.getAlphabet(), oldNet.getStateFactory(), false);
		mRepresentatives = new UnionFind<>();
		constructNet(bp, oldNet);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
		assert petriNetLanguageEquivalence(oldNet, mNet) : "The language recognized by the FinitePrefix2PetriNet is "
				+ "not equal to the language of the original net.";
	}

	@SuppressWarnings("squid:S1698")
	private void constructNet(final BranchingProcess<L, C> bp, final BoundedPetriNet<L, C> oldNet) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("CONDITIONS:");
			for (final Condition<L, C> c : bp.getConditions()) {
				mLogger.debug(c);
			}
			mLogger.debug("EVENTS:");
			for (final Event<L, C> e : bp.getEvents()) {
				mLogger.debug(e.getPredecessorConditions() + " || " + e + " || " + e.getSuccessorConditions());
			}
		}

		/*
		final List<Event<L, C>> events = new ArrayList<>();
		final List<Event<L, C>> worklist = new LinkedList<Event<L, C>>();
		final Set<Event<L, C>> visited = new HashSet<>();
		
		for (final Event<L, C> e : bp.getMinEvents()) {
			worklist.add(e);
			events.add(e);
			visited.add(e);
		}
		while (!worklist.isEmpty()) {
			final Event<L, C> event = worklist.remove(0);
			for (final Condition<L, C> c : event.getSuccessorConditions()) {
				for (final Event<L, C> e : c.getSuccessorEvents()) {
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

		final TreeSet<Event<L, C>> events = new TreeSet<>(bp.getOrder());
		events.addAll(bp.getEvents());

		for (final Condition<L, C> c : bp.getDummyRoot().getSuccessorConditions()) {
			mRepresentatives.makeEquivalenceClass(c);
		}
		final Iterator<Event<L, C>> it = events.iterator();
		final Event<L, C> first = it.next();
		// equality intended here
		assert first == bp.getDummyRoot();
		Event<L, C> previous;
		Event<L, C> current = first;
		while (it.hasNext()) {
			previous = current;
			current = it.next();
			assert bp.getOrder().compare(previous, current) < 0;

			for (final Condition<L, C> c : current.getConditionMark()) {
				final Condition<L, C> representative = mRepresentatives.find(c);
				if (representative == null) {
					mRepresentatives.makeEquivalenceClass(c);
				}
			}

			if (current.isCutoffEvent()) {
				final Event<L, C> companion = current.getCompanion();
				final ConditionMarking<L, C> companionCondMark = companion.getConditionMark();
				final ConditionMarking<L, C> eCondMark = current.getConditionMark();
				mergeConditions(companionCondMark, eCondMark);
				mergeConditions(companion.getPredecessorConditions(), current.getPredecessorConditions());
			}

		}

		final Map<Condition<L, C>, Place<L, C>> placeMap = new HashMap<>();
		for (final Condition<L, C> c : bp.getConditions()) {
			assert mRepresentatives.find(c) != null;
			// equality intended here
			if (c == mRepresentatives.find(c)) {
				final Place<L, C> place = mNet.addPlace(mStateFactory.finitePrefix2net(c),
						bp.initialConditions().contains(c), bp.isAccepting(c));
				placeMap.put(c, place);
			}
		}
		final TransitionSet transitionSet = new TransitionSet();
		for (final Event<L, C> e : events) {
			// equality intended here
			if (e == bp.getDummyRoot()) {
				continue;
			}
			final Set<Place<L, C>> preds = new HashSet<>();
			final Set<Place<L, C>> succs = new HashSet<>();

			for (final Condition<L, C> c : e.getPredecessorConditions()) {
				final Condition<L, C> representative = mRepresentatives.find(c);
				preds.add(placeMap.get(representative));
			}

			for (final Condition<L, C> c : e.getSuccessorConditions()) {
				final Condition<L, C> representative = mRepresentatives.find(c);
				succs.add(placeMap.get(representative));
			}
			transitionSet.addTransition(e.getTransition().getSymbol(), preds, succs);
			// mNet.addTransition(e.getTransition().getSymbol(), preds, succs);
		}
		transitionSet.addAllTransitionsToNet(mNet);

		/*
		for (final Condition<L, C> c : bp.getConditions()) {
			if (!c.getPredecessorEvent().isCutoffEvent()) {
				final Place<L, C> place = mNet.addPlace(old_net.getStateFactory()
						.finitePrefix2net(c), bp.initialConditions()
								.contains(c),
						bp.isAccepting(c));
				placeMap.put(c, place);
			}
		}
		mLogger.debug("CONDITIONS TO PLACE:");
		for (final Map.Entry<Condition<L, C>, Place<L, C>> en : placeMap.entrySet()) {
			mLogger.debug(en);
		}
		for (final Event<L, C> e : bp.getEvents()) {
			if (e.getTransition() == null) {
				continue;
			}
			final ArrayList<Place<L, C>> preds = new ArrayList<>();
			final ArrayList<Place<L, C>> succs = new ArrayList<>();
			for (final Condition<L, C> pc : e.getPredecessorConditions()) {
				assert placeMap.containsKey(pc) : pc.toString()
						+ " has successors, hence cannot be child of cut-off event." +
						" So it must have been added, but it cannot be found.";
				preds.add(placeMap.get(pc));
			}
			Event<L, C> companionOrE = e;
			if (e.isCutoffEvent()) {
				companionOrE = e.getCompanion();
			}
			for (final Condition<L, C> sc : companionOrE.getSuccessorConditions()) {
				assert placeMap.containsKey(sc);
				succs.add(placeMap.get(sc));
			}
			final Transition<L, C> transition = mNet.addTransition(e.getTransition()
					.getSymbol(), preds, succs);
			transitionMap.put(e, transition);
		}
		*/
	}

	private boolean petriNetLanguageEquivalence(final BoundedPetriNet<L, C> oldNet, final BoundedPetriNet<L, C> newNet)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing Petri net language equivalence");
		}

		// TODO Christian 2017-02-15 Cast is temporary workaround, state factory should become a parameter
		final INwaInclusionStateFactory<C> stateFactory = (INwaInclusionStateFactory<C>) oldNet.getStateFactory();
		final INestedWordAutomaton<L, C> finAuto1 = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) oldNet.getStateFactory(), oldNet)).getResult();
		final INestedWordAutomaton<L, C> finAuto2 = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) oldNet.getStateFactory(), newNet)).getResult();
		final NestedRun<L, C> subsetCounterex =
				new IsIncluded<>(mServices, stateFactory, finAuto1, finAuto2).getCounterexample();
		final boolean subset = subsetCounterex == null;
		if (!subset && mLogger.isErrorEnabled()) {
			mLogger.error("Only accepted by first: " + subsetCounterex.getWord());
		}
		final NestedRun<L, C> supersetCounterex =
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
		return "Finished " + getOperationName() + ". Result " + mNet.sizeInformation();
	}

	@Override
	public BoundedPetriNet<L, C> getResult() {
		return mNet;
	}

	/*
	private Condition<L, C> getRepresentative(final Condition<L, C> c) {
		Condition<L, C> result = c;
		while (result != representatives.get(result)) {
			result = representatives.get(result);
			assert result != null;
		}
		return result;
	}
	*/

	private void mergeConditions(final Iterable<Condition<L, C>> set1, final Iterable<Condition<L, C>> set2) {
		final Map<Place<L, C>, Condition<L, C>> origPlace2Condition = new HashMap<>();
		for (final Condition<L, C> cond1 : set1) {
			origPlace2Condition.put(cond1.getPlace(), cond1);
		}

		for (final Condition<L, C> cond2 : set2) {
			final Place<L, C> p2 = cond2.getPlace();
			final Condition<L, C> c1 = origPlace2Condition.get(p2);
			final Condition<L, C> c1representative = mRepresentatives.find(c1);
			assert c1representative != null;

			final Condition<L, C> c2representative = mRepresentatives.find(cond2);
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
		private final Map<L, Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>>> mLetter2Predset2Succsets = new HashMap<>();

		void addTransition(final L letter, final Set<Place<L, C>> predset, final Set<Place<L, C>> succset) {
			Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>> predsets2succsets = mLetter2Predset2Succsets.get(letter);
			if (predsets2succsets == null) {
				predsets2succsets = new HashMap<>();
				mLetter2Predset2Succsets.put(letter, predsets2succsets);
			}
			Set<Set<Place<L, C>>> succsets = predsets2succsets.get(predset);
			if (succsets == null) {
				succsets = new HashSet<>();
				predsets2succsets.put(predset, succsets);
			}
			succsets.add(succset);
		}

		void addAllTransitionsToNet(final BoundedPetriNet<L, C> net) {
			for (final Entry<L, Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>>> entry1 : mLetter2Predset2Succsets
					.entrySet()) {
				final L letter = entry1.getKey();
				final Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>> predsets2succsets = entry1.getValue();
				for (final Entry<Set<Place<L, C>>, Set<Set<Place<L, C>>>> entry2 : predsets2succsets.entrySet()) {
					final Set<Place<L, C>> predset = entry2.getKey();
					final Set<Set<Place<L, C>>> succsets = entry2.getValue();
					for (final Set<Place<L, C>> succset : succsets) {
						final List<Place<L, C>> predList = new ArrayList<>(predset);
						final List<Place<L, C>> succList = new ArrayList<>(succset);
						net.addTransition(letter, predList, succList);
					}
				}
			}
		}
	}
}
