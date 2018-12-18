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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An {@link DisjunctiveAbstractState} is an abstract state that consists of many abstract states of the same type. It
 * represents a disjunction of all these states.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <ACTION>
 * @param <IProgramVarOrConst>
 */
public class DisjunctiveAbstractState<STATE extends IAbstractState<STATE>>
		implements IAbstractState<DisjunctiveAbstractState<STATE>> {

	private final Set<STATE> mStates;
	private final int mMaxSize;

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
				a -> !(a instanceof DisjunctiveAbstractState<?>)) : "Cannot nest AbstractMultiStates, use flatten() instead";
		assert states.size() <= maxSize : "Set too large";
		mMaxSize = maxSize;
		mStates = states;
	}

	private boolean haveSameVars(final Set<STATE> states) {
		if (states.size() <= 1) {
			return true;
		}
		final Set<IProgramVarOrConst> firstVars = states.iterator().next().getVariables();
		return states.stream().allMatch(a -> firstVars.equals(a.getVariables()));
	}

	@Override
	public DisjunctiveAbstractState<STATE> addVariable(final IProgramVarOrConst variable) {
		return map(a -> a.addVariable(variable));
	}

	@Override
	public DisjunctiveAbstractState<STATE> removeVariable(final IProgramVarOrConst variable) {
		return map(a -> a.removeVariable(variable));
	}

	@Override
	public DisjunctiveAbstractState<STATE> addVariables(final Collection<IProgramVarOrConst> variables) {
		return map(a -> a.addVariables(variables));
	}

	@Override
	public DisjunctiveAbstractState<STATE> removeVariables(final Collection<IProgramVarOrConst> variables) {
		return map(a -> a.removeVariables(variables));
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mStates.stream().anyMatch(a -> a.containsVariable(var));
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		if (mStates.isEmpty()) {
			return Collections.emptySet();
		}
		return Collections.unmodifiableSet(mStates.iterator().next().getVariables());
	}

	@Override
	public DisjunctiveAbstractState<STATE>
			renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return map(a -> a.renameVariables(old2newVars));
	}

	@Override
	public DisjunctiveAbstractState<STATE> patch(final DisjunctiveAbstractState<STATE> dominator) {
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
	public boolean isEqualTo(final DisjunctiveAbstractState<STATE> other) {
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
	public SubsetResult isSubsetOf(final DisjunctiveAbstractState<STATE> other) {
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
	public DisjunctiveAbstractState<STATE> intersect(final DisjunctiveAbstractState<STATE> other) {
		assert other != null && other.getVariables().equals(getVariables()) : "Cannot intersect incompatible states";
		return crossProduct((a, b) -> a.intersect(b), other, mStates.size() * other.mStates.size());
	}

	@Override
	public DisjunctiveAbstractState<STATE> union(final DisjunctiveAbstractState<STATE> other) {
		assert other != null && other.getVariables().equals(getVariables()) : "Cannot merge incompatible states";
		final Set<STATE> set = newSet(mStates, other.mStates);
		return new DisjunctiveAbstractState<>(mMaxSize, reduce(set));
	}

	public DisjunctiveAbstractState<STATE> saturatedUnion(final DisjunctiveAbstractState<STATE> other) {
		assert other != null && other.getVariables().equals(getVariables()) : "Cannot merge incompatible states";
		final Set<STATE> set = newSet(mStates, other.mStates);
		return new DisjunctiveAbstractState<>(mMaxSize, reduceByTopologicalOrder(set, mMaxSize));
	}

	/**
	 * Apply the {@link IVariableProvider#defineVariablesAfter(Object, IAbstractState, IAbstractState)} function to all
	 * states in this multi-state. This state acts as local pre state, and all states in hierachicalPreState are used as
	 * hierachical pre states.
	 */
	public <ACTION> DisjunctiveAbstractState<STATE> defineVariablesAfter(
			final IVariableProvider<STATE, ACTION> varProvider, final ACTION transition,
			final DisjunctiveAbstractState<STATE> hierachicalPreState) {
		return crossProduct((a, b) -> varProvider.defineVariablesAfter(transition, a, b), hierachicalPreState,
				mMaxSize);
	}

	/**
	 * Apply the {@link IVariableProvider#createValidPostOpStateAfterLeaving(Object, IAbstractState, IAbstractState)}
	 * function to all states in this multi-state. This state acts as local pre state, and all states in
	 * hierachicalPreState are used as hierachical pre states.
	 */
	public <ACTION> DisjunctiveAbstractState<STATE> createValidPostOpStateAfterLeaving(
			final IVariableProvider<STATE, ACTION> varProvider, final ACTION act,
			final DisjunctiveAbstractState<STATE> hierachicalPreState) {
		if (hierachicalPreState == null) {
			return map(a -> varProvider.createValidPostOpStateAfterLeaving(act, a, null));
		}
		return crossProduct((a, b) -> varProvider.createValidPostOpStateAfterLeaving(act, a, b), hierachicalPreState,
				mStates.size() * hierachicalPreState.mStates.size());
	}

	@Override
	public DisjunctiveAbstractState<STATE> compact() {
		final Set<STATE> compactedStates = newSet(mStates.size());
		final Set<IProgramVarOrConst> vars = new HashSet<>();
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

			final Set<IProgramVarOrConst> missing = new HashSet<>(vars);
			missing.removeAll(state.getVariables());
			if (missing.isEmpty()) {
				compactedSynchronizedStates.add(state);
			} else {
				compactedSynchronizedStates.add(state.addVariables(missing));
			}
		}

		return new DisjunctiveAbstractState<>(mMaxSize, compactedSynchronizedStates);
	}

	public <ACTION> DisjunctiveAbstractState<STATE>
			createValidPostOpStateBeforeLeaving(final IVariableProvider<STATE, ACTION> varProvider, final ACTION act) {
		return map(a -> varProvider.createValidPostOpStateBeforeLeaving(act, a));
	}

	public <ACTION> DisjunctiveAbstractState<STATE> apply(final IAbstractTransformer<STATE, ACTION> op,
			final ACTION transition) {
		return mapCollection(a -> op.apply(a, transition));
	}

	public <ACTION> DisjunctiveAbstractState<STATE> apply(final IAbstractPostOperator<STATE, ACTION> postOp,
			final DisjunctiveAbstractState<STATE> multiStateBeforeLeaving, final ACTION transition) {
		return crossProductCollection((a, b) -> postOp.apply(b, a, transition), multiStateBeforeLeaving, mMaxSize);
	}

	public DisjunctiveAbstractState<STATE> widen(final IAbstractStateBinaryOperator<STATE> op,
			final DisjunctiveAbstractState<STATE> other) {
		// custom cross-product: first, merge the second operand to one state, then perform the default cross product
		final Set<STATE> others;
		if (other.mStates.size() > 1) {
			others = reduceByOrderedMerge(other.mStates, 1);
		} else {
			others = other.mStates;
		}
		final Set<STATE> newSet = newSet(mStates.size());
		for (final STATE localState : mStates) {
			for (final STATE otherState : others) {
				newSet.add(op.apply(localState, otherState));
			}
		}
		if (newSet.equals(mStates)) {
			return this;
		}

		return new DisjunctiveAbstractState<>(mMaxSize, reduceByTopologicalOrder(newSet, mMaxSize));
	}

	/**
	 * Creates one {@link DisjunctiveAbstractState} from a Collection of states, even if these states are already
	 * {@link DisjunctiveAbstractState}s, essentially flattening the disjunction.
	 */
	@SuppressWarnings("unchecked")
	public static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE>
			createDisjunction(final Collection<STATE> states) {
		final Set<STATE> disjuncts = new HashSet<>();
		for (final STATE state : states) {
			if (state instanceof DisjunctiveAbstractState<?>) {
				disjuncts.addAll(((DisjunctiveAbstractState<STATE>) state).getStates());
			} else {
				disjuncts.add(state);
			}
		}
		return new DisjunctiveAbstractState<>(reduce(disjuncts, disjuncts.size()));
	}

	@SuppressWarnings("unchecked")
	public static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE>
			createDisjunction(final Collection<STATE> states, final int maxSize) {
		final Set<STATE> disjuncts = new HashSet<>();
		for (final STATE state : states) {
			if (state instanceof DisjunctiveAbstractState<?>) {
				disjuncts.addAll(((DisjunctiveAbstractState<STATE>) state).getStates());
			} else {
				disjuncts.add(state);
			}
		}
		return new DisjunctiveAbstractState<>(maxSize, reduce(disjuncts, maxSize));
	}

	/**
	 * Compute the union of a collection of states using ordered merge. If states is empty or null this returns null.
	 */
	@SuppressWarnings("unchecked")
	public static <STATE extends IAbstractState<STATE>> STATE union(final Collection<STATE> states) {
		if (states == null || states.isEmpty()) {
			return null;
		}
		if (states.size() == 1) {
			return states.iterator().next();
		}
		final Set<STATE> disjuncts = new HashSet<>(states.size());
		for (final STATE state : states) {
			if (state instanceof DisjunctiveAbstractState<?>) {
				disjuncts.addAll(((DisjunctiveAbstractState<STATE>) state).getStates());
			} else {
				disjuncts.add(state);
			}
		}
		final Set<STATE> result = reduce(disjuncts, 1);
		if (result.isEmpty()) {
			return null;
		}
		assert result.size() == 1;
		return result.iterator().next();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mMaxSize;
		result = prime * result + mStates.hashCode();
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
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DisjunctiveAbstractState<?> other = (DisjunctiveAbstractState<?>) obj;
		if (mMaxSize != other.mMaxSize) {
			return false;
		}
		return mStates.equals(other.mStates);
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
	private DisjunctiveAbstractState<STATE> crossProduct(final BiFunction<STATE, STATE, STATE> funCreateState,
			final DisjunctiveAbstractState<STATE> otherMultiState, final int maxSize,
			final IReduceUntil<STATE> funReduceToSize) {
		final Set<STATE> newSet = newSet(mStates.size() * otherMultiState.mStates.size());
		for (final STATE localState : mStates) {
			for (final STATE otherState : otherMultiState.mStates) {
				newSet.add(funCreateState.apply(localState, otherState));
			}
		}
		if (newSet.equals(mStates)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(maxSize, funReduceToSize.reduce(newSet, maxSize));
	}

	/**
	 * Create a new {@link DisjunctiveAbstractState} by applying some function to each pair of states from this
	 * {@link DisjunctiveAbstractState} and some other {@link DisjunctiveAbstractState} (i.e., the first argument is a
	 * state from this instance). If the resulting set of states does not differ from this state, return this state. If
	 * it differs, create a new {@link DisjunctiveAbstractState} that retains as many as <code>maxSize</code>
	 * disjunctive states.
	 */
	private DisjunctiveAbstractState<STATE> crossProduct(final BiFunction<STATE, STATE, STATE> funCreateState,
			final DisjunctiveAbstractState<STATE> otherMultiState, final int maxSize) {
		return crossProduct(funCreateState, otherMultiState, maxSize, DisjunctiveAbstractState::reduce);
	}

	/**
	 * Same as {@link #crossProduct(BiFunction, DisjunctiveAbstractState, int)}, but the function creates a collection
	 * of states.
	 */
	private DisjunctiveAbstractState<STATE> crossProductCollection(
			final BiFunction<STATE, STATE, Collection<STATE>> funCreateState,
			final DisjunctiveAbstractState<STATE> otherMultiState, final int maxSize) {
		final Set<STATE> newSet = newSet(mStates.size() * otherMultiState.mStates.size());
		for (final STATE localState : mStates) {
			for (final STATE otherState : otherMultiState.mStates) {
				newSet.addAll(funCreateState.apply(localState, otherState));
			}
		}
		if (newSet.equals(mStates)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(maxSize, reduce(newSet));
	}

	private DisjunctiveAbstractState<STATE> map(final Function<STATE, STATE> func) {
		final Set<STATE> newSet = newSet(mStates.size());
		for (final STATE state : mStates) {
			newSet.add(func.apply(state));
		}
		if (mStates.equals(newSet)) {
			return this;
		}
		return new DisjunctiveAbstractState<>(mMaxSize, newSet);
	}

	private DisjunctiveAbstractState<STATE> mapCollection(final Function<STATE, Collection<STATE>> func) {
		final Set<STATE> newSet = newSet();
		for (final STATE state : mStates) {
			newSet.addAll(func.apply(state));
		}
		return new DisjunctiveAbstractState<>(mMaxSize, reduce(newSet, mMaxSize));
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
		return reduce(states, mMaxSize);
	}

	private static <STATE extends IAbstractState<STATE>> Set<STATE> reduce(final Set<STATE> states, final int maxsize) {
		final Set<STATE> maximalElements = getMaximalElements(states);
		if (maximalElements.size() <= maxsize) {
			return maximalElements;
		}
		return reduceByOrderedMerge(maximalElements, maxsize);
	}

	private static <STATE extends IAbstractState<STATE>> Set<STATE> reduceByOrderedMerge(final Set<STATE> states,
			final int maxSize) {
		final STATE first = states.iterator().next();
		return first.union(states, maxSize);
	}

	private static <STATE extends IAbstractState<STATE>> Set<STATE> getMaximalElements(final Set<STATE> states) {
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

	/**
	 * Compute a {@link HashRelation} that represents the partial order on this set of states. An element (a,b) in the
	 * relation states that a is a subset of b. We always add artificial top or bottom elements which are represented by
	 * null.
	 *
	 * In (null,b), the null value represents the bottom element. In (a, null), the null value represents the top
	 * element.
	 *
	 */
	private static <STATE extends IAbstractState<STATE>> List<STATE> getTopologicalOrder(final Set<STATE> states) {
		final IPartialComparator<STATE> comparator = new IPartialComparator<STATE>() {

			@Override
			public ComparisonResult compare(final STATE first, final STATE second) {
				final SubsetResult firstIsCoveredSecond = first.isSubsetOf(second);
				switch (firstIsCoveredSecond) {
				case EQUAL:
					return ComparisonResult.EQUAL;
				case STRICT:
					return ComparisonResult.STRICTLY_SMALLER;
				case NON_STRICT:
				case NONE:
				default:
					break;
				}

				final SubsetResult secondIsCoveredfirst = second.isSubsetOf(first);
				switch (secondIsCoveredfirst) {
				case EQUAL:
					throw new AssertionError("Equal is symmetric");
				case STRICT:
					return ComparisonResult.STRICTLY_GREATER;
				case NON_STRICT:
				case NONE:
				default:
					return ComparisonResult.INCOMPARABLE;
				}
			}
		};
		final PartialOrderCache<STATE> poCache = new PartialOrderCache<>(comparator);
		states.forEach(poCache::addElement);
		final List<STATE> result = poCache.getReverseTopologicalOrdering();
		assert hasDescendingOrder(result) : "states are not in descending order";
		return result;
	}

	private static <STATE extends IAbstractState<STATE>> boolean hasDescendingOrder(final List<STATE> result) {
		final Iterator<STATE> iterator = result.iterator();
		STATE current = null;
		STATE last = null;
		while (iterator.hasNext()) {
			last = current;
			current = iterator.next();
			if (last == null || current == null) {
				continue;
			}
			final SubsetResult covering = current.isSubsetOf(last);
			switch (covering) {
			case EQUAL:
				return false;
			case NONE:
				break;
			case NON_STRICT:
			case STRICT:
			default:
				continue;
			}

			final SubsetResult isCovered = last.isSubsetOf(current);
			switch (isCovered) {
			case EQUAL:
			case STRICT:
				return false;
			case NONE:
			case NON_STRICT:
			default:
				continue;
			}
		}
		return true;
	}

	/**
	 * Reduce the supplied set of states s.t. only maxSize elements remain. Use topological order on the supplied states
	 * to determine which states have to be merged. Merge the smallest states.
	 *
	 * @param states
	 * @param maxSize
	 * @return
	 */
	private static <STATE extends IAbstractState<STATE>> Set<STATE> reduceByTopologicalOrder(final Set<STATE> states,
			final int maxSize) {
		if (states.size() <= maxSize) {
			return states;
		}
		final List<STATE> ordered = getTopologicalOrder(states);
		final Set<STATE> rtr = newSet(maxSize);
		final Iterator<STATE> iter = ordered.iterator();

		// take n-1 allowed elements directly from the topological order
		int i = 1;
		while (iter.hasNext() && i < maxSize) {
			final STATE current = iter.next();
			rtr.add(current);
			++i;
		}
		if (iter.hasNext()) {
			final Set<STATE> mergeDown = new HashSet<>();
			iter.forEachRemaining(mergeDown::add);
			final Set<STATE> reduced = reduce(mergeDown, 1);
			rtr.add(reduced.iterator().next());
		}
		assert rtr.size() <= maxSize : "reduceByTopologicalOrder left too many states";
		return rtr;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private interface IReduceUntil<STATE> {
		Set<STATE> reduce(Set<STATE> states, int maxSize);
	}

}
