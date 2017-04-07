/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.weakener;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * {@link InterpolantSequenceWeakener} tries to weaken each predicate in a sequence of predicates s.t. it is still
 * inductive relative to a given sequence of letters.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public abstract class InterpolantSequenceWeakener<HTC extends IHoareTripleChecker, P extends IPredicate, LETTER extends IAction> {

	private final List<P> mResult;
	protected final ILogger mLogger;
	protected final HTC mHtc;
	private final P mPrecondition;
	private final P mPostcondition;
	protected final Script mScript;
	protected final BasicPredicateFactory mPredicateFactory;
	private final TripleList<P, LETTER> mTripleList;
	protected final Map<PredicateLetterIdentifier<P, LETTER>, P> mHierarchicalPreStates;

	/**
	 * Default constructor. Generates result directly.
	 *
	 * @param logger
	 *            A logger instance.
	 * @param htc
	 *            The {@link IHoareTripleChecker} that should be used to perform the reduction.
	 * @param predicates
	 *            The sequence of {@link IPredicate}s that should be reduced.
	 * @param trace
	 *            The sequence of LETTERs that connects each predicate.
	 */
	public InterpolantSequenceWeakener(final ILogger logger, final HTC htc, final List<P> predicates,
			final List<LETTER> trace, final P precondition, final P postcondition, final Script script,
			final BasicPredicateFactory predicateFactory) {
		mLogger = logger;
		mHtc = Objects.requireNonNull(htc);
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mScript = script;
		mPredicateFactory = predicateFactory;
		mTripleList = new TripleList<>(predicates, trace, mPrecondition, mPostcondition);
		final List<LETTER> checkedTrace = Objects.requireNonNull(trace, "trace is null");
		final List<P> checkedPredicates = Objects.requireNonNull(predicates, "predicates are null");
		if (checkedTrace.size() != checkedPredicates.size() + 1) {
			throw new IllegalStateException("Trace and predicates do not match - their size is incorrect");
		}

		mHierarchicalPreStates = generateCallHierarchicalPreStates(predicates, trace);
		mResult = generateResult(checkedPredicates, checkedTrace);

		if (mResult.size() != predicates.size()) {
			throw new IllegalStateException("The size of the produced result list is invalid.");
		}
	}

	/**
	 * Generates for the call sequence the hierarchical prestates.
	 *
	 * @param predicates
	 *            The states.
	 * @param trace
	 *            The sequence of statements.
	 * @return A map containing prestate to corresponding hierarchical prestate.
	 */
	private Map<PredicateLetterIdentifier<P, LETTER>, P> generateCallHierarchicalPreStates(final List<P> predicates,
			final List<LETTER> trace) {
		final Map<PredicateLetterIdentifier<P, LETTER>, P> returnMap = new HashMap<>();
		final Deque<P> hierarchicalCallStates = new ArrayDeque<>();
		final Iterator<StateTriple<P, LETTER>> it = mTripleList.getIterator();

		while (it.hasNext()) {
			final StateTriple<P, LETTER> triple = it.next();
			if (triple.getTransition() instanceof ICallAction) {
				hierarchicalCallStates.addFirst(triple.getFirstState());
			} else if (triple.getTransition() instanceof IReturnAction) {
				final PredicateLetterIdentifier<P, LETTER> predLetter =
						new PredicateLetterIdentifier<>(triple.getFirstState(), triple.getTransition());
				assert !returnMap.containsKey(predLetter);
				final P hierState = hierarchicalCallStates.removeFirst();
				returnMap.put(predLetter, hierState);
			}
		}

		return returnMap;
	}

	private List<P> generateResult(final List<P> predicates, final List<LETTER> list) {
		assert list != null;

		final TripleList<P, LETTER> tripleList = new TripleList<>(predicates, list, mPrecondition, mPostcondition);
		final TripleList.TripleListReverseIterator<P, LETTER> it = tripleList.getReverseIterator();

		if (!it.hasNext()) {
			throw new IllegalStateException("There is no letter in the list to analyze.");
		}

		StateTriple<P, LETTER> currentStateTriple = it.next();
		P currentPostState = currentStateTriple.getSecondState();

		// Reverse iterate over the list.
		final List<P> returnList = new ArrayList<>();
		while (true) {
			final P currentPreState = currentStateTriple.getFirstState();
			final LETTER transition = currentStateTriple.getTransition();

			assert checkIfInductive(currentPreState, transition, currentPostState,
					mHtc) : "Prestate and poststate are not inductive under the current transition.";

			// If the currentPreState corresponds to the precondition, we arrived at the top, therefore break.
			if (currentPreState == mPrecondition) {
				break;
			}

			final P refinedState = refinePreState(currentPreState, transition, currentPostState);
			returnList.add(refinedState);
			currentPostState = refinedState;

			if (it.hasNext()) {
				currentStateTriple = it.next();
			} else {
				break;
			}
		}

		Collections.reverse(returnList);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Predicate list before weakening   : "
					+ predicates.stream().map(pred -> pred.getFormula()).collect(Collectors.toList()));
			mLogger.debug("New predicate list after weakening: "
					+ returnList.stream().map(pred -> pred.getFormula()).collect(Collectors.toList()));
		}
		return returnList;

	}

	/**
	 * Checks whether a prestate and a post state are inductive under some transition. This method is only for debugging
	 * purposes (with enabled assertions) as inductivity should also be checked outside of this class.
	 *
	 * @param preState
	 *            The prestate.
	 * @param transition
	 *            The transition.
	 * @param postState
	 *            The poststate.
	 * @return <code>true</code> iff inductive, <code>false</code> otherwise.
	 *
	 * @deprecated For debugging purposes only.
	 */
	@Deprecated
	protected final boolean checkIfInductive(final P preState, final LETTER transition, final P postState,
			final IHoareTripleChecker htc) {
		assert preState != null;
		assert transition != null;
		assert postState != null;
		assert htc != null;

		final Validity validity;

		if (transition instanceof IInternalAction) {
			validity = mHtc.checkInternal(preState, (IInternalAction) transition, postState);
		} else if (transition instanceof ICallAction) {
			validity = mHtc.checkCall(preState, (ICallAction) transition, postState);
		} else if (transition instanceof IReturnAction) {
			final PredicateLetterIdentifier<P, LETTER> predLetter =
					new PredicateLetterIdentifier<>(preState, transition);
			final P hierState = mHierarchicalPreStates.get(predLetter);
			assert hierState != null;
			final IReturnAction returnTransition = (IReturnAction) transition;
			validity = mHtc.checkReturn(preState, hierState, returnTransition, postState);
		} else {
			throw new IllegalStateException(
					"The transition has an unsupported type: " + transition.getClass().getSimpleName());
		}

		if (validity == Validity.VALID) {
			return true;
		}

		return false;
	}

	/**
	 * States whether with the given information (pre, transition, post) the prestate can be refined
	 *
	 * @param preState
	 *            The prestate.
	 * @param transition
	 *            The transition.
	 * @param postState
	 *            The poststate.
	 * @return A (hopefully) refined prestate.
	 */
	protected abstract P refinePreState(final P preState, final LETTER transition, final P postState);

	/**
	 * @return the (hopefully) weakened sequence of predicates that is still inductive.
	 */
	public List<P> getResult() {
		return mResult;
	}

	/**
	 * Represents a triple of two states (predicates) and a transition.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 * @param <P>
	 *            The type of the states (predicates).
	 * @param <LETTER>
	 *            The type of the transition.
	 */
	private static final class StateTriple<P, LETTER> {
		private final P mFirstState;
		private final P mSecondState;
		private final LETTER mTransition;

		public StateTriple(final P firstState, final LETTER transition, final P secondState) {
			mFirstState = firstState;
			mSecondState = secondState;
			mTransition = transition;
		}

		public P getFirstState() {
			return mFirstState;
		}

		public P getSecondState() {
			return mSecondState;
		}

		public LETTER getTransition() {
			return mTransition;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("{").append(mFirstState).append("} ").append(mTransition).append(" {").append(mSecondState)
					.append("}");
			return sb.toString();
		}
	}

	/**
	 * Represents a list of triples consisting of states (predicates) and transitions of the form {st1} tr {st2}, where
	 * st1, st2 are states and tr is a transition.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 * @param <P>
	 *            The type of the states (predicates).
	 * @param <LETTER>
	 *            The type of the transition.
	 */
	private static final class TripleList<P, LETTER> {
		private final List<P> mPredicates;
		private final List<LETTER> mTrace;
		private final P mPostcondition;
		private final P mPrecondition;

		private TripleList(final List<P> predicates, final List<LETTER> trace, final P precondition,
				final P postcondition) {
			mPredicates = predicates;
			mTrace = trace;
			mPrecondition = precondition;
			mPostcondition = postcondition;
		}

		private Iterator<StateTriple<P, LETTER>> getIterator() {
			return new TripleListIterator<>(mPredicates, mTrace, mPrecondition, mPostcondition);
		}

		private final TripleListReverseIterator<P, LETTER> getReverseIterator() {
			return new TripleListReverseIterator<P, LETTER>(mPredicates, mTrace, mPrecondition, mPostcondition);
		}

		/**
		 * An iterator to iterate through a list of predicates and letters.
		 *
		 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
		 *
		 * @param <P>
		 *            The type of the predicates.
		 * @param <LETTER>
		 *            The type of the letters.
		 */
		private static final class TripleListIterator<P, LETTER> implements Iterator<StateTriple<P, LETTER>> {

			private final List<P> mPredicates;
			private final List<LETTER> mTrace;
			private final P mPostcondition;
			private final P mPrecondition;

			private int mLetterIndex;

			private TripleListIterator(final List<P> predicates, final List<LETTER> trace, final P precondition,
					final P postcondition) {
				mPredicates = predicates;
				mTrace = trace;
				mPrecondition = precondition;
				mPostcondition = postcondition;
				mLetterIndex = 0;
			}

			@Override
			public boolean hasNext() {
				return mLetterIndex < mTrace.size();
			}

			@Override
			public StateTriple<P, LETTER> next() {
				// The predicate list does not contain pre- and postconditions.
				// Account for this fact here: The first letter leads from the precondition to the first predicate;
				// the last letter leads from the last predicate to the postcondition.
				final P prev;
				if (mLetterIndex == 0) {
					prev = mPrecondition;
				} else {
					prev = mPredicates.get(mLetterIndex - 1);
				}

				final LETTER letter = mTrace.get(mLetterIndex);

				final P next;
				if (mLetterIndex == mTrace.size() - 1) {
					next = mPostcondition;
				} else {
					next = mPredicates.get(mLetterIndex);
				}

				mLetterIndex++;
				return new StateTriple<>(prev, letter, next);
			}
		}

		/**
		 * A reverse iterator to iterate through the list reversely.
		 *
		 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
		 *
		 * @param <P>
		 *            The type of the predicates.
		 * @param <LETTER>
		 *            The type of the letters.
		 */
		private static final class TripleListReverseIterator<P, LETTER> implements Iterator<StateTriple<P, LETTER>> {
			private final List<P> mPredicates;
			private final List<LETTER> mTrace;
			private final P mPostcondition;
			private final P mPrecondition;

			private int mLetterIndex;

			private TripleListReverseIterator(final List<P> predicates, final List<LETTER> trace, final P precondition,
					final P postcondition) {
				mPredicates = predicates;
				mTrace = trace;
				mPrecondition = precondition;
				mPostcondition = postcondition;
				mLetterIndex = mTrace.size() - 1;
			}

			@Override
			public boolean hasNext() {
				return mLetterIndex >= 0;
			}

			@Override
			public StateTriple<P, LETTER> next() {
				// The predicate list does not contain pre- and postconditions.
				// Account for this fact here: The first letter leads from the precondition to the first predicate;
				// the last letter leads from the last predicate to the postcondition.

				final P prev;
				if (mLetterIndex == 0) {
					prev = mPrecondition;
				} else {
					prev = mPredicates.get(mLetterIndex - 1);
				}

				final LETTER letter = mTrace.get(mLetterIndex);

				final P next;
				if (mLetterIndex == mTrace.size() - 1) {
					next = mPostcondition;
				} else {
					next = mPredicates.get(mLetterIndex);
				}

				mLetterIndex--;
				return new StateTriple<>(prev, letter, next);
			}
		}
	}

	/**
	 * Pair constructed from a predicate and a letter for comparison and putting into hashmaps.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 * @param <P>
	 *            The type of the predicate stored in this class.
	 * @param <LETTER>
	 *            The type of the letter stored in this class.
	 */
	protected static final class PredicateLetterIdentifier<P extends IPredicate, LETTER extends IAction> {
		private final P mPredicate;
		private final LETTER mLetter;

		protected PredicateLetterIdentifier(final P predicate, final LETTER letter) {
			mPredicate = predicate;
			mLetter = letter;
		}

		protected P getPredicate() {
			return mPredicate;
		}

		protected LETTER getLetter() {
			return mLetter;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (mLetter == null ? 0 : mLetter.hashCode());
			result = prime * result + (mPredicate == null ? 0 : mPredicate.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (!(obj instanceof PredicateLetterIdentifier)) {
				return false;
			}
			final PredicateLetterIdentifier<?, ?> other = (PredicateLetterIdentifier<?, ?>) obj;
			if (mLetter == null) {
				if (other.mLetter != null) {
					return false;
				}
			} else if (!mLetter.equals(other.mLetter)) {
				return false;
			}
			if (mPredicate == null) {
				if (other.mPredicate != null) {
					return false;
				}
			} else if (!mPredicate.equals(other.mPredicate)) {
				return false;
			}
			return true;
		}
	}
}
