/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.counting.datastructures;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Data structure for counting automata that uses mainly unmodifiable data
 * structures to avoid unintended modifications.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CountingAutomatonDataStructure<LETTER, STATE> implements IAutomaton<LETTER, STATE> {

	private final AutomataLibraryServices mServices;

	private final Set<LETTER> mAlphabet;
	private final LinkedHashSet<STATE> mStates;
	private final Set<String> mCounters;
	private final Map<STATE, Set<ConjunctiveCounterFormula>> mInitialConditions = new HashMap<STATE, Set<ConjunctiveCounterFormula>>();
	private final Map<STATE, Set<ConjunctiveCounterFormula>> mAcceptingConditions = new HashMap<STATE, Set<ConjunctiveCounterFormula>>();
	private final Map<STATE, List<ConjunctiveTransition<LETTER, STATE>>> mOutgoingTransitions = new HashMap<>();

	public CountingAutomatonDataStructure(final AutomataLibraryServices services, final Set<LETTER> alphabet,
			final Set<String> counters) {
		mServices = services;
		mAlphabet = alphabet;
		mCounters = counters;
		mStates = new LinkedHashSet<>();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return Collections.unmodifiableSet(mAlphabet);
	}

	public Set<STATE> getStates() {
		return Collections.unmodifiableSet(mStates);
	}

	public Set<String> getCounters() {
		return Collections.unmodifiableSet(mCounters);
	}

	public Map<STATE, Set<ConjunctiveCounterFormula>> getInitialConditions() {
		return Collections.unmodifiableMap(mInitialConditions);
	}

	public Map<STATE, Set<ConjunctiveCounterFormula>> getAcceptingConditions() {
		return Collections.unmodifiableMap(mAcceptingConditions);
	}

	public boolean addState(final STATE state, final Set<ConjunctiveCounterFormula> initialCondition,
			final Set<ConjunctiveCounterFormula> acceptingCondition) {
		mInitialConditions.put(state, initialCondition);
		mAcceptingConditions.put(state, acceptingCondition);
		return mStates.add(state);
	}

	public void addOutgoingTransition(final ConjunctiveTransition<LETTER, STATE> trans) {
		List<ConjunctiveTransition<LETTER, STATE>> existing = mOutgoingTransitions.get(trans.getPredecessor());
		if (existing == null) {
			existing = new ArrayList<ConjunctiveTransition<LETTER, STATE>>();
			mOutgoingTransitions.put(trans.getPredecessor(), existing);
		}
		existing.add(trans);
	}

	public List<ConjunctiveTransition<LETTER, STATE>> getOutgoingTransitions(final STATE predecessor) {
		final List<ConjunctiveTransition<LETTER, STATE>> result = mOutgoingTransitions.get(predecessor);
		if (result == null) {
			return Collections.emptyList();
		} else {
			return Collections.unmodifiableList(result);
		}
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return mStates.size() + " states.";
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException("cannot transform to ultimate model");
	}

	@Override
	public String toString() {
		return (AutomatonDefinitionPrinter.toString(mServices, "ca", this));
	}
}