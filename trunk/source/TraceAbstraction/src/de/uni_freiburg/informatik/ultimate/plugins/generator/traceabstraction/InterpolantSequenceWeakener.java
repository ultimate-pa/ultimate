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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Iterator;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
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
	private final ILogger mLogger;
	private final HTC mHtc;

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
			final List<LETTER> trace) {
		mLogger = logger;
		mHtc = Objects.requireNonNull(htc);
		final List<LETTER> checkedTrace = Objects.requireNonNull(trace, "trace is null");
		final List<P> checkedPredicates = Objects.requireNonNull(predicates, "predicates are null");
		if (checkedTrace.size() != checkedPredicates.size() + 1) {
			throw new IllegalStateException("Trace and predicates do not match - their size is incorrect");
		}

		mResult = generateResult(checkedPredicates, checkedTrace);

		if (mResult.size() != predicates.size()) {
			throw new IllegalStateException("The size of the produced result list is invalid.");
		}
	}

	private List<P> generateResult(final List<P> predicates, final List<LETTER> list) {
		// Reverse iterate over the list.
		final TripleList<P, LETTER> tripleList = new TripleList<>(predicates, list);
		final Iterator<StateTriple<P, LETTER>> it = tripleList.iterator();
		while (it.hasNext()) {
			final StateTriple<P, LETTER> triple = it.next();
			triple.getFirstState();
			triple.getTransition();
			triple.getSecondState();
		}

		return null;
	}

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
	private static final class TripleList<P, LETTER> implements Iterable<StateTriple<P, LETTER>> {
		private final List<P> mPredicates;
		private final List<LETTER> mTrace;

		public TripleList(final List<P> predicates, final List<LETTER> trace) {
			mPredicates = predicates;
			mTrace = trace;
		}

		@Override
		public Iterator<StateTriple<P, LETTER>> iterator() {
			final Iterator<StateTriple<P, LETTER>> it = new Iterator<StateTriple<P, LETTER>>() {

				private final int mLetterIndex = mTrace.size() - 1;

				@Override
				public boolean hasNext() {
					return mLetterIndex > 0;
				}

				@Override
				public StateTriple<P, LETTER> next() {
					return new StateTriple<>(mPredicates.get(mLetterIndex - 1), mTrace.get(mLetterIndex),
							mPredicates.get(mLetterIndex + 1));
				}
			};
			return it;
		}
	}
}
