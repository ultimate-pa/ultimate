/*
 * Copyright (C) 2015-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * An {@link DisjunctiveAbstractState} is an abstract state that consists of many abstract states of the same type. It
 * represents a disjunction of all these states.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <ACTION>
 * @param <VARDECL>
 */
public class DisjunctiveAbstractState<STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		implements IAbstractState<DisjunctiveAbstractState<STATE, VARDECL>, VARDECL> {

	private static int sNextFreeId;
	private final Set<STATE> mStates;
	private final int mMaxSize;
	private final int mId;

	public DisjunctiveAbstractState() {
		this(Collections.emptySet());
	}

	public DisjunctiveAbstractState(final int maxSize, final STATE state) {
		this(maxSize, Collections.singleton(state));
	}

	public DisjunctiveAbstractState(final STATE state) {
		this(1, Collections.singleton(state));
	}

	private DisjunctiveAbstractState(final Set<STATE> state) {
		this(state.size(), state);
	}

	private DisjunctiveAbstractState(final int maxSize, final Set<STATE> states) {
		assert states != null;
		assert haveSameVars(states);
		assert states.stream().allMatch(
				a -> !(a instanceof DisjunctiveAbstractState<?, ?>)) : "Cannot nest AbstractMultiStates, use flatten() instead";
		mMaxSize = maxSize;
		mStates = states;
		sNextFreeId++;
		mId = sNextFreeId;
	}

	private boolean haveSameVars(final Set<STATE> states) {
		if (states.size() <= 1) {
			return true;
		}
		final Set<VARDECL> firstVars = states.iterator().next().getVariables();
		return states.stream().allMatch(a -> firstVars.equals(a.getVariables()));
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> addVariable(final VARDECL variable) {
		return map(a -> a.addVariable(variable));
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> removeVariable(final VARDECL variable) {
		return map(a -> a.removeVariable(variable));
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> addVariables(final Collection<VARDECL> variables) {
		return map(a -> a.addVariables(variables));
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> removeVariables(final Collection<VARDECL> variables) {
		return map(a -> a.removeVariables(variables));
	}

	@Override
	public boolean containsVariable(final VARDECL var) {
		return mStates.stream().anyMatch(a -> a.containsVariable(var));
	}

	@Override
	public Set<VARDECL> getVariables() {
		if (mStates.isEmpty()) {
			return Collections.emptySet();
		}
		return Collections.unmodifiableSet(mStates.iterator().next().getVariables());
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> renameVariables(final Map<VARDECL, VARDECL> old2newVars) {
		return map(a -> a.renameVariables(old2newVars));
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> patch(final DisjunctiveAbstractState<STATE, VARDECL> dominator) {
		assert mStates.size() != dominator.mStates
				.size() : "Cannot apply symmetrical with differently sized multi-states";
		final Set<STATE> newSet = newSet(mStates.size());
		final Iterator<STATE> iter = mStates.iterator();
		final Iterator<STATE> otherIter = dominator.mStates.iterator();
		while (iter.hasNext() && otherIter.hasNext()) {
			newSet.add(iter.next().patch(otherIter.next()));
		}
		return new DisjunctiveAbstractState<>(mMaxSize, newSet);
	}

	@Override
	public boolean isEmpty() {
		return mStates.stream().anyMatch(a -> a.isEmpty());
	}

	@Override
	public boolean isBottom() {
		return mStates.isEmpty() || mStates.stream().allMatch(a -> a.isBottom());
	}

	@Override
	public boolean isEqualTo(final DisjunctiveAbstractState<STATE, VARDECL> other) {
		if (other == null) {
			return false;
		}
		if (!other.getVariables().equals(getVariables())) {
			return false;
		}

		for (final STATE state : mStates) {
			if (!other.mStates.stream().anyMatch(state::isEqualTo)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public SubsetResult isSubsetOf(final DisjunctiveAbstractState<STATE, VARDECL> other) {
		if (other == null) {
			return SubsetResult.NONE;
		}

		if (other.isBottom() && isBottom()) {
			return SubsetResult.EQUAL;
		}
		if (other.isBottom()) {
			return SubsetResult.NONE;
		}
		if (isBottom()) {
			return SubsetResult.STRICT;
		}

		if (!other.getVariables().equals(getVariables())) {
			return SubsetResult.NONE;
		}
		if (other.mStates.isEmpty() && !mStates.isEmpty()) {
			return SubsetResult.NONE;
		}

		SubsetResult result = SubsetResult.EQUAL;
		for (final STATE state : mStates) {
			SubsetResult max = SubsetResult.NONE;
			for (final STATE otherState : other.mStates) {
				max = state.isSubsetOf(otherState).max(max);
			}
			result = result.min(max);
			if (result == SubsetResult.NONE) {
				break;
			}
		}
		return result;
	}

	@Override
	public EvalResult evaluate(final Script script, final Term term) {
		boolean allFalse = true;
		for (final STATE state : mStates) {
			final EvalResult result = state.evaluate(script, term);
			if (result == EvalResult.TRUE) {
				return result;
			} else if (result == EvalResult.UNKNOWN) {
				allFalse = false;
			}
		}
		if (allFalse) {
			return EvalResult.FALSE;
		}
		return EvalResult.UNKNOWN;
	}

	@Override
	public Term getTerm(final Script script) {
		return SmtUtils.or(script, mStates.stream().map(a -> a.getTerm(script)).collect(Collectors.toSet()));
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('#').append(mStates.size());
		for (final STATE state : mStates) {
			sb.append('{');
			final String logStr = state.toLogString();
			if (logStr == null || logStr.isEmpty()) {
				sb.append("__");
			} else {
				sb.append(logStr);
			}
			sb.append('}');
			sb.append(", ");
		}
		if (!mStates.isEmpty()) {
			sb.delete(sb.length() - 2, sb.length());
		}
		return sb.toString();
	}

	@Override
	public int hashCode() {
		return mId;
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
		final DisjunctiveAbstractState<?, ?> other = (DisjunctiveAbstractState<?, ?>) obj;
		if (mId != other.mId) {
			return false;
		}
		if (mStates == null) {
			if (other.mStates != null) {
				return false;
			}
		} else if (!mStates.equals(other.mStates)) {
			return false;
		}
		return true;
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> intersect(final DisjunctiveAbstractState<STATE, VARDECL> other) {
		assert other != null && other.getVariables().equals(getVariables()) : "Cannot intersect incompatible states";
		return crossProduct((a, b) -> a.intersect(b), other, mStates.size() * other.mStates.size());
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> union(final DisjunctiveAbstractState<STATE, VARDECL> other) {
		assert other != null && other.getVariables().equals(getVariables()) : "Cannot merge incompatible states";
		final Set<STATE> set = newSet(mStates, other.mStates);
		return new DisjunctiveAbstractState<>(mMaxSize, reduce(set));
	}

	/**
	 * Apply the {@link IVariableProvider#defineVariablesAfter(Object, IAbstractState, IAbstractState)} function to all
	 * states in this multi-state. This state acts as local pre state, and all states in hierachicalPreState are used as
	 * hierachical pre states.
	 */
	public <ACTION> DisjunctiveAbstractState<STATE, VARDECL> defineVariablesAfter(
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final ACTION transition,
			final DisjunctiveAbstractState<STATE, VARDECL> hierachicalPreState) {
		return crossProduct((a, b) -> varProvider.defineVariablesAfter(transition, a, b), hierachicalPreState,
				mMaxSize);
	}

	/**
	 * Apply the {@link IVariableProvider#createValidPostOpStateAfterLeaving(Object, IAbstractState, IAbstractState)}
	 * function to all states in this multi-state. This state acts as local pre state, and all states in
	 * hierachicalPreState are used as hierachical pre states.
	 */
	public <ACTION> DisjunctiveAbstractState<STATE, VARDECL> createValidPostOpStateAfterLeaving(
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final ACTION act,
			final DisjunctiveAbstractState<STATE, VARDECL> hierachicalPreState) {
		if (hierachicalPreState == null) {
			return map(a -> varProvider.createValidPostOpStateAfterLeaving(act, a, null));
		}
		return crossProduct((a, b) -> varProvider.createValidPostOpStateAfterLeaving(act, a, b), hierachicalPreState,
				mStates.size() * hierachicalPreState.mStates.size());
	}

	@Override
	public DisjunctiveAbstractState<STATE, VARDECL> compact() {
		final Set<STATE> compactedStates = newSet(mStates.size());
		final Set<VARDECL> vars = new HashSet<>();
		for (final STATE state : mStates) {
			final STATE compacted = state.compact();
			compactedStates.add(compacted);
			vars.addAll(compacted.getVariables());
		}
		if (mStates.equals(compactedStates)) {
			return this;
		}

		final Set<STATE> compactedSynchronizedStates = newSet(mStates.size());
		for (final STATE state : compactedStates) {

			final Set<VARDECL> missing = new HashSet<>(vars);
			missing.removeAll(state.getVariables());
			if (missing.isEmpty()) {
				compactedSynchronizedStates.add(state);
			} else {
				compactedSynchronizedStates.add(state.addVariables(missing));
			}
		}

		return new DisjunctiveAbstractState<>(mMaxSize, compactedSynchronizedStates);
	}

	public <ACTION> DisjunctiveAbstractState<STATE, VARDECL> createValidPostOpStateBeforeLeaving(
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final ACTION act) {
		return map(a -> varProvider.createValidPostOpStateBeforeLeaving(act, a));
	}

	public <ACTION> DisjunctiveAbstractState<STATE, VARDECL>
			apply(final IAbstractTransformer<STATE, ACTION, VARDECL> op, final ACTION transition) {
		return mapCollection(a -> op.apply(a, transition));
	}

	public <ACTION> DisjunctiveAbstractState<STATE, VARDECL> apply(
			final IAbstractPostOperator<STATE, ACTION, VARDECL> postOp,
			final DisjunctiveAbstractState<STATE, VARDECL> multiStateBeforeLeaving, final ACTION transition) {
		return crossProductCollection((a, b) -> postOp.apply(b, a, transition), multiStateBeforeLeaving, mMaxSize);
	}

	public DisjunctiveAbstractState<STATE, VARDECL> apply(final IAbstractStateBinaryOperator<STATE> op,
			final DisjunctiveAbstractState<STATE, VARDECL> other) {
		return crossProduct(op::apply, other, mMaxSize);
	}

	@Override
	public String toString() {
		return toLogString();
	}

	public Set<STATE> getStates() {
		return Collections.unmodifiableSet(mStates);
	}

	public STATE getSingleState(final IAbstractStateBinaryOperator<STATE> mergeOp) {
		return mStates.stream().reduce(mergeOp::apply).orElse(null);
	}

	/**
	 * Create a new {@link DisjunctiveAbstractState} by applying some function to each pair of states from this
	 * {@link DisjunctiveAbstractState} and some other {@link DisjunctiveAbstractState} (i.e., the first argument is a
	 * state from this instance). If the resulting set of states does not differ from this state, return this state. If
	 * it differs, create a new {@link DisjunctiveAbstractState} that retains as many as <code>maxSize</code>
	 * disjunctive states.
	 */
	private DisjunctiveAbstractState<STATE, VARDECL> crossProduct(final BiFunction<STATE, STATE, STATE> funCreateState,
			final DisjunctiveAbstractState<STATE, VARDECL> otherMultiState, final int maxSize) {
		final Set<STATE> newSet = newSet(mStates.size() * otherMultiState.mStates.size());
		for (final STATE localState : mStates) {
			for (final STATE otherState : otherMultiState.mStates) {
				newSet.add(funCreateState.apply(localState, otherState));
			}
		}
		if (newSet.equals(mStates)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(maxSize, getMaximalElements(newSet));
	}

	/**
	 * Same as {@link #crossProduct(BiFunction, DisjunctiveAbstractState, int)}, but the function creates a collection
	 * of states.
	 */
	private DisjunctiveAbstractState<STATE, VARDECL> crossProductCollection(
			final BiFunction<STATE, STATE, Collection<STATE>> funCreateState,
			final DisjunctiveAbstractState<STATE, VARDECL> otherMultiState, final int maxSize) {
		final Set<STATE> newSet = newSet(mStates.size() * otherMultiState.mStates.size());
		for (final STATE localState : mStates) {
			for (final STATE otherState : otherMultiState.mStates) {
				newSet.addAll(funCreateState.apply(localState, otherState));
			}
		}
		if (newSet.equals(mStates)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(maxSize, getMaximalElements(newSet));
	}

	private DisjunctiveAbstractState<STATE, VARDECL> map(final Function<STATE, STATE> func) {
		final Set<STATE> newSet = newSet(mStates.size());
		for (final STATE state : mStates) {
			newSet.add(func.apply(state));
		}
		if (mStates.equals(newSet)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(mMaxSize, newSet);
	}

	private DisjunctiveAbstractState<STATE, VARDECL> mapCollection(final Function<STATE, Collection<STATE>> func) {
		final Set<STATE> newSet = newSet();
		for (final STATE state : mStates) {
			newSet.addAll(func.apply(state));
		}
		return new DisjunctiveAbstractState<>(mMaxSize, getMaximalElements(newSet));
	}

	private Set<STATE> newSet() {
		return newSet(mMaxSize);
	}

	private static <STATE> Set<STATE> newSet(final int maxSize) {
		return new LinkedHashSet<>(maxSize, 1.0F);
	}

	@SafeVarargs
	private final Set<STATE> newSet(final Set<STATE>... sets) {
		if (sets == null || sets.length == 0) {
			return newSet();
		}
		final int elems = Arrays.stream(sets).map(a -> a.size()).reduce((a, b) -> a + b).get();
		final Set<STATE> set = newSet(elems);
		Arrays.stream(sets).forEach(set::addAll);
		return set;
	}

	private Set<STATE> reduce(final Set<STATE> states) {
		final Set<STATE> maximalElements = getMaximalElements(states);
		if (maximalElements.size() <= mMaxSize) {
			return maximalElements;
		}
		return reduceByOrderedMerge(maximalElements);
	}

	private Set<STATE> reduceByOrderedMerge(final Set<STATE> states) {
		final Set<STATE> reducibleSet = new LinkedHashSet<>(states);
		int numberOfMerges = states.size() - mMaxSize;
		while (numberOfMerges > 0) {
			final Iterator<STATE> iter = reducibleSet.iterator();
			final STATE first = iter.next();
			iter.remove();
			final STATE second = iter.next();
			iter.remove();
			if (reducibleSet.add(first.union(second))) {
				--numberOfMerges;
			} else {
				numberOfMerges -= 2;
			}
		}
		assert reducibleSet.size() <= mMaxSize;
		return reducibleSet;
	}

	/**
	 * Creates one {@link DisjunctiveAbstractState} from a Collection of states, even if these states are already
	 * {@link DisjunctiveAbstractState}s, essentially flattening the disjunction.
	 */
	@SuppressWarnings("unchecked")
	public static <STATE extends IAbstractState<STATE, VARDECL>, VARDECL> DisjunctiveAbstractState<STATE, VARDECL>
			createDisjunction(final Collection<STATE> states) {

		final Set<STATE> disjuncts = new HashSet<>();
		for (final STATE state : states) {
			if (state instanceof DisjunctiveAbstractState<?, ?>) {
				disjuncts.addAll(((DisjunctiveAbstractState<STATE, VARDECL>) state).getStates());
			} else {
				disjuncts.add(state);
			}
		}
		return new DisjunctiveAbstractState<>(reduce(disjuncts, disjuncts.size()));
	}

	private static <STATE extends IAbstractState<STATE, VARDECL>, VARDECL> Set<STATE> reduce(final Set<STATE> states,
			final int maxsize) {
		final Set<STATE> maximalElements = getMaximalElements(states);
		if (maximalElements.size() <= maxsize) {
			return maximalElements;
		}
		return reduceByOrderedMerge(maximalElements, maxsize);
	}

	private static <STATE extends IAbstractState<STATE, VARDECL>, VARDECL> Set<STATE>
			reduceByOrderedMerge(final Set<STATE> states, final int maxsize) {
		final Set<STATE> reducibleSet = new LinkedHashSet<>(states);
		int numberOfMerges = states.size() - maxsize;
		while (numberOfMerges > 0) {
			final Iterator<STATE> iter = reducibleSet.iterator();
			final STATE first = iter.next();
			iter.remove();
			final STATE second = iter.next();
			iter.remove();
			if (reducibleSet.add(first.union(second))) {
				--numberOfMerges;
			} else {
				numberOfMerges -= 2;
			}
		}
		assert reducibleSet.size() <= maxsize;
		return reducibleSet;
	}

	private static <STATE extends IAbstractState<STATE, VARDECL>, VARDECL> Set<STATE>
			getMaximalElements(final Set<STATE> states) {
		if (states.isEmpty() || states.size() == 1) {
			return states;
		}
		final Set<STATE> maximalElements = newSet(states.size());
		for (final STATE state : states) {
			final Iterator<STATE> iter = maximalElements.iterator();
			boolean maximal = true;
			while (iter.hasNext()) {
				final STATE candidate = iter.next();
				final SubsetResult stateIsCovered = state.isSubsetOf(candidate);
				final SubsetResult stateCovers = candidate.isSubsetOf(state);
				if (stateIsCovered != SubsetResult.NONE) {
					// state is covered by someone, it cannot be maximal
					maximal = false;
					break;
				}
				if (stateCovers != SubsetResult.NONE) {
					// state covers someone
					iter.remove();
				}
			}

			if (maximal) {
				maximalElements.add(state);
			}
		}
		assert maximalElements.stream().filter(STATE::isBottom).count() <= 1 : "There can be only one bottom element";
		return maximalElements;
	}

}
