/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Represents a union of multiple coverage relations.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class UnionPredicateCoverageChecker implements IPredicateCoverageChecker {

	private final ImmutableList<Pair<IPredicateCoverageChecker, Predicate<IPredicate>>> mComponents;

	private UnionPredicateCoverageChecker(
			final ImmutableList<Pair<IPredicateCoverageChecker, Predicate<IPredicate>>> components) {
		mComponents = components;
	}

	/**
	 * Creates a union coverage relation with zero operands.
	 *
	 * @return an empty coverage relation
	 */
	public static UnionPredicateCoverageChecker empty() {
		return new UnionPredicateCoverageChecker(ImmutableList.empty());
	}

	/**
	 * Adds another operand to the union.
	 *
	 * @param checker
	 *            An additional coverage relation to add to the union
	 * @param protection
	 *            An optional predicate identifying {@link IPredicate} instances that should not be passed to the given
	 *            coverage relation. {@code null} if no such protection is needed.
	 * @return a coverage relation representing the union of the current instance with the given relation
	 */
	public UnionPredicateCoverageChecker with(final IPredicateCoverageChecker checker,
			final Predicate<IPredicate> protection) {
		return new UnionPredicateCoverageChecker(new ImmutableList<>(new Pair<>(checker, protection), mComponents));
	}

	@Override
	public Validity isCovered(final IPredicate lhs, final IPredicate rhs) {
		for (final var pair : mComponents) {
			final var protection = pair.getSecond();
			if (protection != null && (protection.test(lhs) || protection.test(rhs))) {
				continue;
			}

			final Validity result = pair.getFirst().isCovered(lhs, rhs);
			if (result == Validity.VALID || result == Validity.INVALID) {
				return result;
			}
		}
		return Validity.UNKNOWN;
	}

	@Override
	public Set<IPredicate> getCoveredPredicates(final IPredicate pred) {
		return mComponents.stream()
				.flatMap(p -> p.getSecond() == null || p.getSecond().test(pred)
						? p.getFirst().getCoveredPredicates(pred).stream()
						: Stream.empty())
				.collect(Collectors.toSet());
	}

	@Override
	public Set<IPredicate> getCoveringPredicates(final IPredicate pred) {
		return mComponents.stream()
				.flatMap(p -> p.getSecond() == null || p.getSecond().test(pred)
						? p.getFirst().getCoveringPredicates(pred).stream()
						: Stream.empty())
				.collect(Collectors.toSet());
	}

	@Override
	public IPartialComparator<IPredicate> getPartialComparator() {
		return (p1, p2) -> {
			if (Objects.equals(p1, p2)) {
				return ComparisonResult.EQUAL;
			}
			if (getCoveredPredicates(p1).contains(p2)) {
				return ComparisonResult.STRICTLY_GREATER;
			}
			if (getCoveringPredicates(p1).contains(p1)) {
				return ComparisonResult.STRICTLY_SMALLER;
			}
			return ComparisonResult.INCOMPARABLE;
		};
	}

	@Override
	public HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation() {
		final HashRelation<IPredicate, IPredicate> relation = new HashRelation<>();
		for (final var pair : mComponents) {
			relation.addAll(pair.getFirst().getCopyOfImplicationRelation());
		}
		return relation;
	}
}
