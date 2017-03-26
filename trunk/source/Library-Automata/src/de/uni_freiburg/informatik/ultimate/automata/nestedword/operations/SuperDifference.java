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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a SuperDifference can compute a NWA nwa_difference
 * such that nwa_difference accepts all words that are accepted by nwa_minuend but not by Psi(nwa_subtrahend), i.e.
 * L(nwa_difference) = L(nwa_minuend) \ L( Psi(nwa_subtrahend) ), where Psi is a transformation of the automaton
 * nwa_subtrahend that is defined by an implementation of IStateDeterminizer.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Hättig (haettigj@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of automata. In many cases you want to use
 *            String as STATE and your states are labeled e.g. with "q0", "q1", ...
 */

public final class SuperDifference<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private static final String FOLLOW_LABEL = "follow label ";
	private static final String ADD_TARGET_SINK_STATE_Q2 = "add target (sink) state q2: ";
	private static final String TRAVERSE_IN_SINK_STATE = "Traverse in sink state ";
	private static final String WITH = " with ";
	private static final String AND_DOTS = " and ...";

	private final INestedWordAutomaton<LETTER, STATE> mMinuend;
	private final INestedWordAutomaton<LETTER, STATE> mSubtrahend;
	private final AutomatonEpimorphism<STATE> mEpimorphism;
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	private final STATE mSinkState;
	private final HashMap<String, STATE> mContainedStatesHashMap;
	private final IIntersectionStateFactory<STATE> mStateFactory;

	/**
	 * Computes the an automaton A' which is the over approximation of the difference of the two automatons minuend and
	 * subtrahend such that L(A') >= L(minuend) - L(subtrahend) and L(A') <= L(minuend). Therefore it needs an automaton
	 * epimorphism.
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
	public SuperDifference(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> minuend,
			final INestedWordAutomaton<LETTER, STATE> subtrahend,
			final AutomatonEpimorphism<STATE> automatonEpimorhpism, final boolean minimize)
			throws AutomataOperationCanceledException {
		super(services);
		mMinuend = minuend;
		mSubtrahend = subtrahend;
		mEpimorphism = automatonEpimorhpism;
		// TODO Christian 2017-02-15 Casts are temporary workarounds until state factory becomes constructor parameter
		final ISinkStateFactory<STATE> sinkStateFactory = (ISinkStateFactory<STATE>) minuend.getStateFactory();
		mStateFactory = (IIntersectionStateFactory<STATE>) minuend.getStateFactory();
		mContainedStatesHashMap = new HashMap<>();
		if (minimize && mLogger.isErrorEnabled()) {
			mLogger.error("Minimization not implemented.");
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		// initialize the result with the empty automaton
		mResult = new NestedWordAutomaton<>(mServices, minuend.getInternalAlphabet(), minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(), mStateFactory);
		mSinkState = sinkStateFactory.createSinkStateContent();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Created Sink-State: " + mSinkState.toString());
		}

		// initializes the process by adding the initial states. Since there can
		// be many initial states, it adds all possible initial state pair combinations
		for (final STATE initM : mMinuend.getInitialStates()) {
			STATE initS = mEpimorphism.getMapping(initM);
			if (initS == null || !mSubtrahend.getInitialStates().contains(initS)) {
				initS = mSinkState;
			} else {
				assert mSubtrahend.getStates().contains(initS);
			}
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Add initial state:" + initM + "---" + initS);
			}
			addState(initM, initS);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/* *** *** *** Functions *** *** *** */
	@Override
	public String operationName() {
		return "SuperDifference";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Minuend " + mMinuend.sizeInformation() + " Subtrahend "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + mResult.sizeInformation();
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getFirstOperand() {
		return mMinuend;
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getSecondOperand() {
		return mSubtrahend;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	// TODO Christian 2016-09-04: unused method
	String bl(final boolean b) {
		return b ? "T" : "F";
	}

	/**
	 * (for computing the super difference) Adds a state into the result automaton. Respectively adds all necessary
	 * transitions and states.
	 * 
	 * @param r
	 *            first part of the label of the state
	 * @param s
	 *            second part of the label of the state
	 * @return the state in the new automaton
	 */
	@SuppressWarnings("squid:S1698")
	private STATE addState(final STATE r, final STATE s) {
		assert mMinuend.getStates().contains(r);
		// equality intended here
		assert s == mSinkState || mSubtrahend.getStates().contains(s);

		// if it does already exist, return that state
		final String qLabel = r.toString() + '|' + s.toString();
		final STATE existingState = mContainedStatesHashMap.get(qLabel);
		if (existingState != null) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("State for " + qLabel + " already exists: " + existingState.toString());
			}
			return existingState;
		}

		// if not: create a new state "q" and add it into the superDifference automaton
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Add state: " + qLabel + " created from: " + r.toString() + " and " + s.toString());
		}
		final STATE intersection = mStateFactory.intersection(r, s);
		if (intersection == null && mLogger.isErrorEnabled()) {
			mLogger.error("State factory returned no state!");
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("intersection: " + intersection);
		}
		mContainedStatesHashMap.put(qLabel, intersection);

		// equality intended here
		final boolean isInitial = mMinuend.isInitial(r) && (s == mSinkState || mSubtrahend.isInitial(s));
		// equality intended here
		final boolean isFinal = mMinuend.isFinal(r) && (s == mSinkState || !mSubtrahend.isFinal(s));

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("isFinal: " + isFinal);
			mLogger.debug("isIniti: " + isInitial);
		}

		mResult.addState(isInitial, isFinal, intersection);

		// get the epimorph state
		final STATE hR = mEpimorphism.getMapping(r);

		// check if there exists a mapping to r in the epimorphism
		// equality intended here
		if (hR == s) {
			addStateNormalState(r, s, intersection, hR);
		} else {
			addStateSinkState(r, s, intersection, hR);
		}

		return intersection;
	}

	private void addStateSinkState(final STATE r, final STATE s, final STATE intersection, final STATE hR) {
		// we are in the sink state in the subtrahend automaton
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("No epimorph state found: hr:" + hR + " r:" + r + " s: " + s);
		}

		// Traverse all edges = (r, label, r2) \in \delta
		addStateSinkStateInternal(r, intersection);
		addStateSinkStateCall(r, intersection);
		addStateSinkStateReturn(r, intersection);
	}

	private void addStateSinkStateInternal(final STATE r, final STATE intersection) {
		for (final OutgoingInternalTransition<LETTER, STATE> e : mMinuend.internalSuccessors(r)) {
			// we know that we must take the sink state, since there is no epimorph state
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(FOLLOW_LABEL + e.getLetter() + AND_DOTS);
				mLogger.debug(ADD_TARGET_SINK_STATE_Q2 + e.getSucc());
			}
			final STATE q2 = addState(e.getSucc(), mSinkState);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(TRAVERSE_IN_SINK_STATE + intersection + WITH + e.getLetter() + " to " + q2.toString());
			}
			mResult.addInternalTransition(intersection, e.getLetter(), q2);
		}
	}

	private void addStateSinkStateCall(final STATE r, final STATE intersection) {
		for (final OutgoingCallTransition<LETTER, STATE> e : mMinuend.callSuccessors(r)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(FOLLOW_LABEL + e.getLetter() + AND_DOTS);
				mLogger.debug(ADD_TARGET_SINK_STATE_Q2 + e.getSucc());
			}
			final STATE q2 = addState(e.getSucc(), mSinkState);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(TRAVERSE_IN_SINK_STATE + intersection + WITH + e.getLetter() + " to " + q2.toString());
			}
			mResult.addCallTransition(intersection, e.getLetter(), q2);
		}
	}

	private void addStateSinkStateReturn(final STATE r, final STATE intersection) {
		for (final OutgoingReturnTransition<LETTER, STATE> e : mMinuend.returnSuccessors(r)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(FOLLOW_LABEL + e.getLetter() + AND_DOTS);
				mLogger.debug(ADD_TARGET_SINK_STATE_Q2 + e.getSucc());
			}

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

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(TRAVERSE_IN_SINK_STATE + intersection + WITH + e.getLetter() + " to " + q2.toString());
			}
		}
	}

	private void addStateNormalState(final STATE r, final STATE s, final STATE intersection, final STATE hR) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("epimorph state: " + hR.toString());
		}
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
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("found hier pred state mapping:" + mapping.toString());
				}
				final STATE hierPred = addState(e.getHierPred(), mapping);
				traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
			} else if (mLogger.isDebugEnabled()) {
				mLogger.debug("found sink no hier pred mapping, took sink state");
			}
			final STATE hierPred = addState(e.getHierPred(), mSinkState);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("hier pred is: " + hierPred);
			}
			traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
		}
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
	private void traverseEdge(final ITransitionlet<LETTER, STATE> e, final STATE r, final STATE s, final STATE q,
			final STATE target, final int edgeType, final STATE hierPred) {
		final LETTER label = e.getLetter();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Traverse edge: from " + r.toString() + WITH + label + " to " + target.toString());
		}

		// get the target state in the subtrahend automaton
		final STATE hR2 = mEpimorphism.getMapping(target);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("mapping of the target is: " + hR2);
		}

		// now we want to check if the subtrahend automaton has an epimorphic state as well

		boolean targetExistsInMinuend = false;
		if (hR2 != null) {
			switch (edgeType) {
				case 0:
					targetExistsInMinuend = findTargetInternal(s, label, hR2);
					break;
				case 1:
					targetExistsInMinuend = findTargetCall(s, label, hR2);
					break;
				case 2:
					targetExistsInMinuend = findTargetReturn(s, hierPred, label, hR2);
					break;
				default:
					throw new IllegalArgumentException();
			}
		}

		// make sure that the target state of the edge q2 exists
		STATE q2;
		if (targetExistsInMinuend) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("target state exists");
			}
			// if that state and the corresponding edge with the same label exists
			q2 = addState(target, hR2);
		} else {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("target state exists not");
			}
			// otherwise we fall in to the sink state
			q2 = addState(target, mSinkState);
		}

		// mLogger.debug("Adding the edge from " + q.toString() + " with " + label + " to " + q2.toString());

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

	@SuppressWarnings("squid:S1698")
	private boolean findTargetInternal(final STATE state, final LETTER label, final STATE hR2) {
		for (final OutgoingInternalTransition<LETTER, STATE> e2 : mSubtrahend.internalSuccessors(state, label)) {
			// equality intended here
			if (e2.getSucc() == hR2) {
				return true;
			}
		}
		return false;
	}

	@SuppressWarnings("squid:S1698")
	private boolean findTargetCall(final STATE state, final LETTER label, final STATE hR2) {
		for (final OutgoingCallTransition<LETTER, STATE> e2 : mSubtrahend.callSuccessors(state, label)) {
			// equality intended here
			if (e2.getSucc() == hR2) {
				return true;
			}
		}
		return false;
	}

	@SuppressWarnings("squid:S1698")
	private boolean findTargetReturn(final STATE state, final STATE hierPred, final LETTER label, final STATE hR2) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("hierPred for " + hierPred);
		}
		for (final OutgoingReturnTransition<LETTER, STATE> e2 : mSubtrahend.returnSuccessors(state, hierPred, label)) {
			// equality intended here
			if (e2.getSucc() == hR2) {
				return true;
			}
		}
		return false;
	}
}
