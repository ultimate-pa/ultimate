/*
 * Copyright (C) 2014-2015 Jan Hättig (haettigj@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * SuperDifference can compute a NWA nwa_difference such that nwa_difference
 * accepts all words that are accepted by nwa_minuend but not by
 * Psi(nwa_subtrahend), i.e. L(nwa_difference) = L(nwa_minuend) \ L(
 * Psi(nwa_subtrahend) ), where Psi is a transformation of the automaton
 * nwa_subtrahend that is defined by an implementation of IStateDeterminizer.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the
 *            automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of
 *            automata. In many cases you want to use String as STATE and your
 *            states are labeled e.g. with "q0", "q1", ...
 */

public class SuperDifference<LETTER, STATE>
		extends GeneralOperation<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/* *** *** *** Fields *** *** *** */
	
	// Automatons
	private final INestedWordAutomaton<LETTER, STATE> mMinuend;
	private final INestedWordAutomaton<LETTER, STATE> mSubtrahend;
	private final AutomatonEpimorphism<STATE> mEpimorphism;
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	private final STATE mSinkState;
	private final HashMap<String, STATE> mContainedStatesHashMap;
	private final StateFactory<STATE> mStateFactory;
	
	/**
	 * Computes the an automaton A' which is the over approximation of the
	 * difference of the two automatons minuend and subtrahend such that L(A')
	 * >= L(minuend) - L(subtrahend) and L(A') <= L(minuend). Therefore it needs
	 * an automaton epimorphism.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param minuend
	 *            the minuend
	 * @param subtrahend
	 *            the subtrahend
	 * @param automatonEpimorhpism
	 *            the automaton epimorphism
	 * @param minimize
	 *            if true, the resulting automaton will be reduced
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public SuperDifference(
			final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> minuend,
			final INestedWordAutomaton<LETTER, STATE> subtrahend,
			final AutomatonEpimorphism<STATE> automatonEpimorhpism,
			final boolean minimize)
					throws AutomataOperationCanceledException {
		super(services);
		mMinuend = minuend;
		mSubtrahend = subtrahend;
		mEpimorphism = automatonEpimorhpism;
		mStateFactory = minuend.getStateFactory();
		mContainedStatesHashMap = new HashMap<String, STATE>();
		if (minimize) {
			mLogger.error("Minimization not implemented.");
		}
		
		mLogger.info(startMessage());
		
		// initialize the result with the empty automaton
		mResult = new NestedWordAutomaton<LETTER, STATE>(
				mServices,
				minuend.getInternalAlphabet(), minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		mSinkState = mStateFactory.createSinkStateContent();
		mLogger.debug("Created Sink-State: " + mSinkState.toString());
		
		// initializes the process by adding the initial states. Since there can
		// be many initial states, it adds all possible initial state pair combinations
		for (final STATE initM : mMinuend.getInitialStates()) {
			STATE initS = mEpimorphism.getMapping(initM);
			if (initS == null || !mSubtrahend.getInitialStates().contains(initS)) {
				initS = mSinkState;
			} else {
				assert (mSubtrahend.getStates().contains(initS));
			}
			mLogger.debug("Add initial state:" + initM + "---" + initS);
			addState(initM, initS);
		}
		mLogger.info(exitMessage());
	}
	
	/* *** *** *** Functions *** *** *** */
	@Override
	public String operationName() {
		return "superDifference";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Minuend "
				+ mMinuend.sizeInformation() + " Subtrahend "
				+ mSubtrahend.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ mResult.sizeInformation();
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	String bl(final boolean b) {
		return b ? "T" : "F";
	}
	
	/**
	 * (for computing the super difference) Adds a state into the result
	 * automaton. Respectively adds all necessary edges and states
	 * 
	 * @param r
	 *            first part of the label of the state
	 * @param s
	 *            second part of the label of the state
	 * @return
	 * 		the state in the new automaton
	 */
	private STATE addState(final STATE r, final STATE s) {
		assert (mMinuend.getStates().contains(r));
		assert (s == mSinkState || mSubtrahend.getStates().contains(s));
		
		// if it does already exist, return that state
		final String qLabel = r.toString() + "|" + s.toString();
		final STATE existingState = mContainedStatesHashMap.get(qLabel);
		if (existingState != null) {
			mLogger.debug("State for " + qLabel + " already exists: "
					+ existingState.toString());
			return existingState;
		}
		
		// if not: create a new state "q" and add it into the superDifference automaton
		mLogger.debug("Add state: " + qLabel + " created from: " + r.toString() + " and " + s.toString());
		final STATE intersection = mStateFactory.intersection(r, s);
		if (intersection == null) {
			mLogger.error("State factory returned no state!");
		}
		mLogger.debug("intersection: " + intersection);
		mContainedStatesHashMap.put(qLabel, intersection);
		
		final boolean isInitial = mMinuend.isInitial(r) && (s == mSinkState || mSubtrahend.isInitial(s));
		final boolean isFinal = mMinuend.isFinal(r) && (s == mSinkState || !mSubtrahend.isFinal(s));
		
		mLogger.debug("isFinal: " + isFinal);
		mLogger.debug("isIniti: " + isInitial);
		
		mResult.addState(isInitial, isFinal, intersection);
		
		// get the epimorph state
		final STATE hR = mEpimorphism.getMapping(r);
		
		// check if there exists a mapping to r in the epimorphism
		if (hR == s) {
			mLogger.debug("epimorph state: " + hR.toString());
			// Traverse all edges = (r, label, r2) \in \delta
			
			for (final OutgoingInternalTransition<LETTER, STATE> e : mMinuend.internalSuccessors(r)) {
				traverseEdge(e, r, s, intersection, e.getSucc(), 0, null);
			}
			
			for (final OutgoingCallTransition<LETTER, STATE> e : mMinuend.callSuccessors(r)) {
				traverseEdge(e, r, s, intersection, e.getSucc(), 1, null);
			}
			
			for (final OutgoingReturnTransition<LETTER, STATE> e : mMinuend.returnSuccessors(r)) {
				// get the hier pred (if not exists this could be created)
				final STATE mapping = mEpimorphism.getMapping(e.getHierPred());
				if (mapping != null) {
					mLogger.debug("found hier pred state mapping:" + mapping.toString());
					final STATE hierPred = addState(e.getHierPred(), mapping);
					traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
				} else {
					mLogger.debug("found sink no hier pred mapping, took sink state");
				}
				final STATE hierPred = addState(e.getHierPred(), mSinkState);
				
				mLogger.debug("hier pred is: " + hierPred);
				traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
			}
		} else {
			// we are in the sink state in the subtrahend automaton
			
			mLogger.debug("No epimorph state found: hr:" + hR + " r:" + r + " s: " + s);
			
			// Traverse all edges = (r, label, r2) \in \delta
			for (final OutgoingInternalTransition<LETTER, STATE> e : mMinuend.internalSuccessors(r)) {
				// we know that we must take the sink state, since there is no epimorph state
				mLogger.debug("follow label " + e.getLetter() + " and ...");
				mLogger.debug("add target (sinked) state q2: " + e.getSucc());
				final STATE q2 = addState(e.getSucc(), mSinkState);
				mLogger.debug(
						"Traverse in sink state " + intersection + " with " + e.getLetter() + " to " + q2.toString());
				mResult.addInternalTransition(intersection, e.getLetter(), q2);
			}
			
			for (final OutgoingCallTransition<LETTER, STATE> e : mMinuend.callSuccessors(r)) {
				mLogger.debug("follow label " + e.getLetter() + " and ...");
				mLogger.debug("add target (sinked) state q2: " + e.getSucc());
				final STATE q2 = addState(e.getSucc(), mSinkState);
				mLogger.debug(
						"Traverse in sink state " + intersection + " with " + e.getLetter() + " to " + q2.toString());
				mResult.addCallTransition(intersection, e.getLetter(), q2);
			}
			
			for (final OutgoingReturnTransition<LETTER, STATE> e : mMinuend.returnSuccessors(r)) {
				mLogger.debug("follow label " + e.getLetter() + " and ...");
				mLogger.debug("add target (sinked) state q2: " + e.getSucc());
				
				final STATE mapping = mEpimorphism.getMapping(e.getHierPred());
				if (mapping != null) {
					// Add the transition's hierarchical predecessor
					final STATE hierPred = addState(e.getHierPred(), mapping);
					// Add the transition's successor
					final STATE q2 = addState(e.getSucc(), mSinkState);
					// Add the transition
					mResult.addReturnTransition(intersection, hierPred, e.getLetter(), q2);
				}
				
				// Add the transition's hierarchical predecessor
				final STATE hierPred = addState(e.getHierPred(), mSinkState);
				// Add the transition's successor
				final STATE q2 = addState(e.getSucc(), mSinkState);
				// Add the transition
				mResult.addReturnTransition(intersection, hierPred, e.getLetter(), q2);
				
				mLogger.debug("Traverse in sink state " + intersection + " with "
						+ e.getLetter() + " to " + q2.toString());
			}
		}
		
		return intersection;
	}
	
	/**
	 * Traverse an edge and add it to the new automatons.
	 * 
	 * @param e
	 *            the outgoing transition
	 * @param r
	 *            the state of the subtrahend
	 * @param s
	 *            the state of the minuend
	 * @param q
	 *            the merged stated
	 * @param target
	 *            the successor of the outgoing transition
	 * @param edgeType
	 *            0:internal, 1:call, 2:return
	 * @param hierPred
	 *            hierarchical predecessor
	 */
	private void traverseEdge(
			final ITransitionlet<LETTER, STATE> e,
			final STATE r,
			final STATE s,
			final STATE q,
			final STATE target,
			final int edgeType,
			final STATE hierPred) {
		final LETTER label = e.getLetter();
		
		mLogger.debug("Traverse edge: from " + r.toString() + " with " + label + " to " + target.toString());
		
		// find/construct the target state of the edge
		STATE q2 = null;
		// get the target state in the subtrahend automaton
		final STATE hR2 = mEpimorphism.getMapping(target);
		mLogger.debug("mapping of the target is: " + hR2);
		
		// now we want to check if the subtrahend automaton has an epimorph state as well
		boolean targetExistsInMinuend = false;
		if (hR2 != null) {
			switch (edgeType) {
				case 0:
					for (final OutgoingInternalTransition<LETTER, STATE> e2 : mSubtrahend.internalSuccessors(s,
							label)) {
						if (e2.getSucc() == hR2) {
							targetExistsInMinuend = true;
							break;
						}
					}
					break;
				case 1:
					for (final OutgoingCallTransition<LETTER, STATE> e2 : mSubtrahend.callSuccessors(s, label)) {
						if (e2.getSucc() == hR2) {
							targetExistsInMinuend = true;
							break;
						}
					}
					break;
				case 2:
					mLogger.debug("hierPred for " + hierPred);
					for (final OutgoingReturnTransition<LETTER, STATE> e2 : mSubtrahend.returnSuccessors(s, hierPred,
							label)) {
						if (e2.getSucc() == hR2) {
							targetExistsInMinuend = true;
							break;
						}
					}
					break;
				default:
					throw new IllegalArgumentException();
			}
		}
		
		// make sure that the target state q2 exists
		if (targetExistsInMinuend) {
			mLogger.debug("target state exists");
			// if that state and the corresponding edge with the same label exists
			q2 = addState(target, hR2);
		} else {
			mLogger.debug("target state exists not");
			// otherwise we fall in to the sink state
			q2 = addState(target, mSinkState);
		}
		
//		mLogger.debug("Adding the edge from " + q.toString() + " with " + label + " to " + q2.toString());
		
		switch (edgeType) {
			case 0:
				mResult.addInternalTransition(q, label, q2);
				break;
			case 1:
				mResult.addCallTransition(q, label, q2);
				break;
			case 2:
				mResult.addReturnTransition(q, hierPred, label, q2);
				break;
			default:
				throw new IllegalArgumentException();
		}
	}
}
