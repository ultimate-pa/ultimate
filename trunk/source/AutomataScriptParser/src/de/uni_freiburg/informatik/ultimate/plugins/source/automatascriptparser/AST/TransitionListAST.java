/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Is used to hold transitions for nestedword automata (internal-, call-, and
 * return-transitions) and for Petri nets.
 * 
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class TransitionListAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 4468320445354864058L;
	private final Map<Pair<String, String>, Set<String>> mTransitions;
	private final Map<String, Map<String, Map<String, Set<String>>>> mReturnTransitions;
	private final List<PetriNetTransitionAST> mnetTransitions;
	private final ArrayList<IdentifierListAST> mIdLists = new ArrayList<IdentifierListAST>();

	public TransitionListAST(final ILocation loc) {
		super(loc);
		mTransitions = new HashMap<Pair<String, String>, Set<String>>();
		mReturnTransitions = new HashMap<String, Map<String, Map<String, Set<String>>>>();
		mnetTransitions = new ArrayList<PetriNetTransitionAST>();
	}

	/**
	 * Method to add an internal or call transition for nested word automaton.
	 * 
	 * @param fromState
	 * @param label
	 * @param toState
	 */
	private void addTransition(final String fromState, final String label, final String toState) {
		final Pair<String, String> stateSymbolPair = new Pair<String, String>(fromState, label);
		if (mTransitions.containsKey(stateSymbolPair)) {
			final Set<String> succs = mTransitions.get(stateSymbolPair);
			succs.add(toState);
			mTransitions.put(stateSymbolPair, succs);
		} else {
			final Set<String> succs = new HashSet<String>();
			succs.add(toState);
			mTransitions.put(stateSymbolPair, succs);
		}
	}

	/**
	 * Method to add a return transition for a nested word automaton.
	 * 
	 * @param fromState
	 * @param returnState
	 * @param label
	 * @param toState
	 */
	private void addTransition(final String fromState, final String returnState, final String label,
			final String toState) {
		Map<String, Map<String, Set<String>>> hier2letter2succs = mReturnTransitions.get(fromState);
		if (hier2letter2succs == null) {
			hier2letter2succs = new HashMap<String, Map<String, Set<String>>>();
			mReturnTransitions.put(fromState, hier2letter2succs);
		}
		Map<String, Set<String>> letter2succs = hier2letter2succs.get(returnState);
		if (letter2succs == null) {
			letter2succs = new HashMap<String, Set<String>>();
			hier2letter2succs.put(returnState, letter2succs);
		}
		Set<String> succs = letter2succs.get(label);
		if (succs == null) {
			succs = new HashSet<String>();
			letter2succs.put(label, succs);
		}
		succs.add(toState);
	}

	public void addTransition(final IdentifierListAST idList) {
		mIdLists.add(idList);
		final List<String> ids = idList.getIdentifierList();
		if (ids.size() == 3) {
			addTransition(ids.get(0), ids.get(1), ids.get(2));
		} else if (ids.size() == 4) {
			addTransition(ids.get(0), ids.get(1), ids.get(2), ids.get(3));
		}
	}

	@Deprecated
	/**
	 * 20180125 Matthias: Deprecated, implement analogously to
	 * convertToEpsilonTransitions()
	 */
	public Map<Pair<String, String>, Set<String>> getTransitions() {
		return mTransitions;
	}

	@Deprecated
	/**
	 * 20180125 Matthias: Deprecated, implement analogously to
	 * convertToEpsilonTransitions()
	 */
	public Map<String, Map<String, Map<String, Set<String>>>> getReturnTransitions() {
		return mReturnTransitions;
	}

	/**
	 * Method to add a transition for Petri nets.
	 * 
	 * @param nt
	 *            the transition of a Petri net
	 */
	public void addNetTransition(final PetriNetTransitionAST nt) {
		mnetTransitions.add(nt);
	}

	public List<PetriNetTransitionAST> getNetTransitions() {
		return mnetTransitions;
	}

	public HashRelation<String, String> convertToEpsilonTransitions() {
		final HashRelation<String, String> result = new HashRelation<>();
		for (final IdentifierListAST idList : mIdLists) {
			if (idList.getIdentifierList().size() != 2) {
				throw new IllegalArgumentException(
						"List of epsilon transitions contains element that is not a pair: " + idList);
			} else {
				result.addPair(idList.getIdentifierList().get(0), idList.getIdentifierList().get(1));
			}
		}
		return result;
	}

}
