/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessAssumption;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class WitnessGuidedAssertOrder<L extends IAction> implements IAssertOrder<L> {
	private final IAssertOrder<L> mUnderlying;

	public WitnessGuidedAssertOrder(final IAssertOrder<L> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final var startEnd = computeStartEnd(counterexample);
		final List<Set<Integer>> underlyingPartitions = mUnderlying.partition(counterexample);
		// We use the following partitioning:
		// 1) We first assert the first and shortest statements between starting with a negated witness assumption
		// and ending with a witness assumption.
		// 2) Then, the statements before this negated witness assumption are asserted.
		// 3) Finally, the statements after this witness assumption are asserted.

		// The first block is already sufficient for infeasibility, if the corresponding invariants in the witness
		// are inductive invariants. If the first invariant is indeed an invariant, but not inductive, we also need
		// to assert the second block. The third block is only necessary, if the second invariant is not an
		// invariant.

		// We could also change the order of the second and third block or merge them, based on the expected
		// invariants to improve the possible performance (i.e., are there more invalid invariants than invariants
		// that are not inductive)
		final Stream<Set<Integer>> betweenInvariants =
				filterPartitions(underlyingPartitions, x -> startEnd.getFirst() <= x && x <= startEnd.getSecond());
		final Stream<Set<Integer>> beforeInvariant =
				filterPartitions(underlyingPartitions, x -> x < startEnd.getFirst());
		final Stream<Set<Integer>> afterInvariant =
				filterPartitions(underlyingPartitions, x -> x > startEnd.getSecond());
		return Stream.concat(betweenInvariants, Stream.concat(beforeInvariant, afterInvariant)).toList();
	}

	private static Stream<Set<Integer>> filterPartitions(final List<Set<Integer>> partitions,
			final Predicate<Integer> filter) {
		return partitions.stream().map(p -> p.stream().filter(filter).collect(Collectors.toSet()))
				.filter(x -> !x.isEmpty());
	}

	private Pair<Integer, Integer> computeStartEnd(final Counterexample<L> counterexample) {
		int end = counterexample.length() - 1;
		for (int i = 0; i < counterexample.length(); i++) {
			if (isMatchingWitnessAssumption(counterexample.getWord().getSymbol(i), true)) {
				end = i;
				break;
			}
		}
		int start = 0;
		for (int i = end; i >= 0; i--) {
			if (isMatchingWitnessAssumption(counterexample.getWord().getSymbol(i), false)) {
				start = i;
				break;
			}
		}
		return new Pair<>(start, end);
	}

	private boolean isMatchingWitnessAssumption(final L action, final boolean isNegated) {
		if (!(action instanceof final IElement element)) {
			return false;
		}
		final WitnessAssumption annot = WitnessAssumption.getAnnotation(element);
		return annot != null && annot.isIsNegated() == isNegated;
	}
}
