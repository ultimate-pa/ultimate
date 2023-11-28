/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * An implementation of an {@link ISleepSetStateFactory} for {@link IPredicate} states. Currently only works with
 * {@link IMLPredicate}s.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the sleep set
 */
public class SleepSetStateFactoryForRefinement<L> implements ISleepSetStateFactory<L, IPredicate, IPredicate> {
	private final IPredicate mEmptyStack;
	private final UnifyHash<SleepPredicate<L>> mUnifier = new UnifyHash<>();

	/**
	 * Creates a new instance from a predicate factory.
	 *
	 * @param predicateFactory
	 *            The predicate factory used to create new MLPredicates.
	 */
	public SleepSetStateFactoryForRefinement(final PredicateFactory predicateFactory) {
		mEmptyStack = predicateFactory.newEmptyStackPredicate();
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmptyStack;
	}

	@Override
	public IPredicate createSleepSetState(final IPredicate state, final ImmutableSet<L> sleepset) {
		final var mlState = (IMLPredicate) state;
		final int hash = SleepPredicate.hashCode(mlState, sleepset);
		for (final var candidate : mUnifier.iterateHashCode(hash)) {
			if (candidate.valueEquals(mlState, sleepset)) {
				return candidate;
			}
		}

		final var newState = new SleepPredicate<>(mlState, sleepset);
		mUnifier.put(hash, newState);
		return newState;
	}

	/**
	 * Retrieves the original state from which a reduction state was constructed.
	 *
	 * @param sleepState
	 *            The state of the sleep set reduction, as returned by a call to
	 *            {@link #createSleepSetState(IPredicate, Set)}.
	 * @return The argument passed to {@link #createSleepSetState(IPredicate, ImmutableSet)} that returned the given
	 *         reduction state
	 */
	@Override
	public IPredicate getOriginalState(final IPredicate sleepState) {
		return ((SleepPredicate<?>) sleepState).getUnderlying();
	}

	/**
	 * Retrieves the sleep set for which a reduction state was constructed.
	 *
	 * @param sleepState
	 *            The state of the sleep set reduction, as returned by a call to
	 *            {@link #createSleepSetState(IPredicate, Set)}.
	 * @return The argument passed to {@link #createSleepSetState(IPredicate, ImmutableSet)} that returned the given
	 *         reduction state
	 */
	@Override
	public ImmutableSet<L> getSleepSet(final IPredicate sleepState) {
		return ((SleepPredicate<L>) sleepState).getSleepSet();
	}

	/**
	 * A predicate annotated with a sleep set.
	 *
	 * @param <L>
	 *            The type of letters in the sleep set
	 */
	public static final class SleepPredicate<L> extends AnnotatedMLPredicate<ImmutableSet<L>> {
		/**
		 * Create a new annotated predicate
		 *
		 * @param underlying
		 *            The underlying predicate being annotated
		 * @param sleepSet
		 *            The sleep set annotating the predicate
		 */
		public SleepPredicate(final IMLPredicate underlying, final ImmutableSet<L> sleepSet) {
			super(underlying, sleepSet);
		}

		public ImmutableSet<L> getSleepSet() {
			return mAnnotation;
		}

		@Override
		public String toString() {
			return "SleepPredicate [underlying: " + mUnderlying + ", sleep set: " + mAnnotation + "]";
		}

		@Override
		public int hashCode() {
			// reproducible hash code
			return hashCode(mUnderlying, mAnnotation);
		}

		private static int hashCode(final IMLPredicate underlying, final ImmutableSet<?> sleepSet) {
			final int prime = 79;
			return HashUtils.hashJenkins(prime, underlying, sleepSet);
		}

		@Override
		public boolean equals(final Object obj) {
			// reference equality, as instances are unified by the factory
			return this == obj;
		}

		private boolean valueEquals(final IMLPredicate underlying, final ImmutableSet<L> sleepSet) {
			return mUnderlying.equals(underlying) && mAnnotation.equals(sleepSet);
		}
	}
}
