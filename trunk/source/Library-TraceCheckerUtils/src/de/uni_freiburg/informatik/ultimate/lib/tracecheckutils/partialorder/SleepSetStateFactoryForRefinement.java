/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.partialorder;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.ICoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

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

	// Can we get rid of this entirely? [Requires reference equality to be replaced with #equals() everywhere.]
	private final Map<IPredicate, Map<ImmutableSet<L>, IPredicate>> mKnownStates = new HashMap<>();

	/**
	 * Creates a new instance from a predicate factory.
	 *
	 * @param predicateFactory
	 *            The predicate factory used to create new MLPredicates.
	 */
	public SleepSetStateFactoryForRefinement(final PredicateFactory predicateFactory) {
		super();
		mEmptyStack = predicateFactory.newEmptyStackPredicate();
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmptyStack;
	}

	@Override
	public IPredicate createSleepSetState(final IPredicate state, final ImmutableSet<L> sleepset) {
		final Map<ImmutableSet<L>, IPredicate> sleep2State = mKnownStates.computeIfAbsent(state, x -> new HashMap<>());
		return sleep2State.computeIfAbsent(sleepset, x -> createFreshCopy(state, sleepset));
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

	public void reset() {
		mKnownStates.clear();
	}

	private IPredicate createFreshCopy(final IPredicate original, final ImmutableSet<L> sleepset) {
		if (!(original instanceof IMLPredicate)) {
			throw new IllegalArgumentException("Unexpected type of predicate: " + original.getClass());
		}
		return new SleepPredicate<>((IMLPredicate) original, sleepset);
	}

	public static final class SleepPredicate<L> implements IMLPredicate {
		private final IMLPredicate mUnderlying;
		private final ImmutableSet<L> mSleepSet;

		public SleepPredicate(final IMLPredicate underlying, final ImmutableSet<L> sleepSet) {
			mUnderlying = underlying;
			mSleepSet = sleepSet;
		}

		@Override
		public IcfgLocation[] getProgramPoints() {
			return mUnderlying.getProgramPoints();
		}

		@Override
		public Term getFormula() {
			return mUnderlying.getFormula();
		}

		@Override
		public Term getClosedFormula() {
			return mUnderlying.getClosedFormula();
		}

		@Override
		public String[] getProcedures() {
			return mUnderlying.getProcedures();
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mUnderlying.getVars();
		}

		@Override
		public Set<IProgramConst> getConstants() {
			return mUnderlying.getConstants();
		}

		@Override
		public Set<IProgramFunction> getFunctions() {
			return mUnderlying.getFunctions();
		}

		@Override
		public int hashCode() {
			return Objects.hash(mSleepSet, mUnderlying);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SleepPredicate<?> other = (SleepPredicate<?>) obj;
			return Objects.equals(mSleepSet, other.mSleepSet) && Objects.equals(mUnderlying, other.mUnderlying);
		}

		public IMLPredicate getUnderlying() {
			return mUnderlying;
		}

		public ImmutableSet<L> getSleepSet() {
			return mSleepSet;
		}
	}

	public static class FactoryCoveringRelation<L> implements ICoveringRelation<IPredicate> {
		private final SleepSetStateFactoryForRefinement<L> mFactory;

		public FactoryCoveringRelation(final SleepSetStateFactoryForRefinement<L> factory) {
			mFactory = factory;
		}

		@Override
		public boolean covers(final IPredicate oldState, final IPredicate newState) {
			assert getKey(oldState) == getKey(newState);
			return mFactory.getSleepSet(newState).containsAll(mFactory.getSleepSet(oldState));
		}

		@Override
		public Object getKey(final IPredicate state) {
			return mFactory.getOriginalState(state);
		}
	}
}
