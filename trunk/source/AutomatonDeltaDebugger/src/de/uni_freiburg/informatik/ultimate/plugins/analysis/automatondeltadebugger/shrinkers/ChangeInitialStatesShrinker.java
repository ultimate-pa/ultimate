/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Swaps initial states.
 * <p>
 * This bridge shrinker swaps the initial states.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class ChangeInitialStatesShrinker<LETTER, STATE> extends BridgeShrinker<Pair<STATE, STATE>, LETTER, STATE> {
	private List<Pair<STATE, STATE>> mPairs;
	private boolean mChangeWasSuccessful;
	private INestedWordAutomaton<LETTER, STATE> mAutomatonBackup;

	/**
	 * Implementation detail: The assignment of the fields is useless.
	 * 
	 * @param services
	 *            Ultimate services.
	 */
	public ChangeInitialStatesShrinker(final IUltimateServiceProvider services) {
		super(services);
		mPairs = null;
		mChangeWasSuccessful = false;
		mAutomatonBackup = null;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(final List<Pair<STATE, STATE>> list) {
		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton = mFactory.create(mAutomatonBackup);

		assert list.size() == 1 : "There should be only one element in the list.";
		final Pair<STATE, STATE> swap = list.get(0);
		final STATE oldInit = swap.getFirst();
		final STATE newInit = swap.getSecond();
		assert mAutomatonBackup.isInitial(oldInit) : "The (supposedly) old initial state not initial.";
		assert !mAutomatonBackup.isInitial(newInit) : "The new initial state was already initial.";

		// add all old states except for the two states passed
		final Set<STATE> oldStates = new HashSet<>(mAutomatonBackup.getStates());
		boolean wasPresent = oldStates.remove(oldInit);
		assert wasPresent;
		wasPresent = oldStates.remove(newInit);
		assert wasPresent;

		for (final STATE state : oldStates) {
			mFactory.addState(automaton, state, mAutomatonBackup.isInitial(state), mAutomatonBackup.isFinal(state));
		}

		// add two transitions with swapped initial status
		mFactory.addState(automaton, oldInit, false, mAutomatonBackup.isFinal(oldInit));
		mFactory.addState(automaton, newInit, true, mAutomatonBackup.isFinal(newInit));

		// add transitions which still remain
		mFactory.addFilteredTransitions(automaton, mAutomatonBackup);

		/*
		 * Update the factory. This is necessary for the "normal" shrinkers to construct the result with respect to the
		 * new initial states.
		 */
		mFactory.setAutomaton(automaton);

		assert sameNumberOfInitialStates(mAutomatonBackup, automaton);

		return automaton;
	}

	@Override
	public List<Pair<STATE, STATE>> extractList() {
		// there are still more things to change
		if (mPairs != null) {
			mChangeWasSuccessful = false;
			// make a copy so we can modify it here
			return new ArrayList<>(mPairs);
		}

		reset(mAutomaton);
		final Iterator<STATE> initialStates = mAutomatonBackup.getInitialStates().iterator();
		if (!initialStates.hasNext()) {
			return Collections.emptyList();
		}
		// just use the first initial state (avoid the combinatorial explosion if there is more than one initial state)
		final STATE init = initialStates.next();
		mPairs = new LinkedList<>();

		// add all pairs of the initial state and any other state
		for (final STATE state : mAutomatonBackup.getStates()) {
			if (mAutomatonBackup.isInitial(state)) {
				continue;
			}
			mPairs.add(new Pair<>(init, state));
		}

		// make a copy so we can modify it here
		return new ArrayList<>(mPairs);
	}

	@Override
	public void reset(final INestedWordAutomaton<LETTER, STATE> automaton) {
		mPairs = null;
		mChangeWasSuccessful = false;
		mAutomatonBackup = automaton;
	}

	@Override
	public boolean isCancelRequested() {
		return mChangeWasSuccessful;
	}

	@Override
	public boolean isFinished() {
		return mPairs.isEmpty();
	}

	@Override
	public void error(final INestedWordAutomaton<LETTER, STATE> newAutomaton) {
		super.error(newAutomaton);
		mChangeWasSuccessful = true;
		mPairs.remove(0);
	}

	@Override
	public void noError(final INestedWordAutomaton<LETTER, STATE> newAutomaton) {
		super.noError(newAutomaton);
		mFactory.setAutomaton(mAutomatonBackup);
		mPairs.remove(0);
	}

	private boolean sameNumberOfInitialStates(final INestedWordAutomaton<LETTER, STATE> automaton1,
			final INestedWordAutomaton<LETTER, STATE> automaton2) {
		final boolean result = automaton1.getInitialStates().size() == automaton2.getInitialStates().size();
		if (!result) {
			return false;
		}
		return result;
	}
}
