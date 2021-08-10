/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.ICoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
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

	private final PredicateFactory mPredicateFactory;
	private final IPredicate mEmptyStack;
	private final Map<IPredicate, Map<ImmutableSet<L>, IPredicate>> mKnownStates = new HashMap<>();
	private final Map<IPredicate, IPredicate> mOriginalStates = new HashMap<>();
	private final Map<IPredicate, Set<L>> mSleepSets;

	/**
	 * Creates a new instance from a predicate factory.
	 *
	 * @param predicateFactory
	 *            The predicate factory used to create new MLPredicates.
	 */
	public SleepSetStateFactoryForRefinement(final PredicateFactory predicateFactory) {
		super();
		mPredicateFactory = predicateFactory;
		mEmptyStack = predicateFactory.newEmptyStackPredicate();
		mSleepSets = PartialOrderCegarLoop.ENABLE_COVERING_OPTIMIZATION ? new HashMap<>() : null;
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
	 * @return The argument passed to {@link #createSleepSetState(IPredicate, Set)} that returned the given reduction
	 *         state
	 */
	public IPredicate getOriginalState(final IPredicate sleepState) {
		return mOriginalStates.get(sleepState);
	}

	private Set<L> getSleepSet(final IPredicate sleepState) {
		return mSleepSets.get(sleepState);
	}

	private IPredicate createFreshCopy(final IPredicate original, final Set<L> sleepset) {
		if (original instanceof MLPredicateWithConjuncts) {
			final MLPredicateWithConjuncts mlPred = (MLPredicateWithConjuncts) original;
			final MLPredicateWithConjuncts copy = mPredicateFactory.construct(
					id -> new MLPredicateWithConjuncts(id, mlPred.getProgramPoints(), mlPred.getConjuncts()));
			mOriginalStates.put(copy, original);
			if (PartialOrderCegarLoop.ENABLE_COVERING_OPTIMIZATION) {
				mSleepSets.put(copy, sleepset);
			}
			return copy;
		}
		if (original instanceof IMLPredicate) {
			final IMLPredicate mlPred = (IMLPredicate) original;
			final IMLPredicate copy = mPredicateFactory.newMLPredicate(mlPred.getProgramPoints(), mlPred.getFormula());
			mOriginalStates.put(copy, original);
			if (PartialOrderCegarLoop.ENABLE_COVERING_OPTIMIZATION) {
				mSleepSets.put(copy, sleepset);
			}
			return copy;
		}
		throw new IllegalArgumentException("Unexpected type of predicate: " + original.getClass());
	}

	public static class FactoryCoveringRelation<L> implements ICoveringRelation<IPredicate> {
		private final SleepSetStateFactoryForRefinement<L> mFactory;

		public FactoryCoveringRelation(final SleepSetStateFactoryForRefinement<L> factory) {
			mFactory = factory;
			assert PartialOrderCegarLoop.ENABLE_COVERING_OPTIMIZATION : "Covering optimization turned off";
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
