/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;

/**
 * A simple implementation of {@link IFloydHoareAnnotation} backed by a map.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            the type of states which are annotated
 */
public class FloydHoareMapping<S> implements IFloydHoareAnnotation<S> {
	private final PrePostConditionSpecification<S> mSpecification;
	private final Map<S, IPredicate> mAnnotation;
	private final IPredicate mDefaultPredicate;

	/**
	 * Create an instance with the given specification, where states that are not included in the given map do not have
	 * any annotation.
	 *
	 * See {@link IFloydHoareAnnotation#getAnnotation(Object)} for an explanation of how not having any annotation
	 * differs from a default predicate (e.g. {@code true}).
	 *
	 * @param specification
	 *            The specification proven by the created instance
	 * @param annotation
	 *            the underlying map from states to their annotations
	 */
	public FloydHoareMapping(final PrePostConditionSpecification<S> specification,
			final Map<S, IPredicate> annotation) {
		this(specification, annotation, null);
	}

	/**
	 * Create an instance with the given specification, and a default fallback predicate for unknown states.
	 *
	 * See {@link IFloydHoareAnnotation#getAnnotation(Object)} for an explanation of how not having any annotation
	 * differs from a default predicate (e.g. {@code true}).
	 *
	 * @param specification
	 *            The specification proven by the created instance
	 * @param annotation
	 *            the underlying map from states to their annotations
	 * @param defaultPredicate
	 *            A default predicate to be returned when no annotation for a given state is known.
	 */
	public FloydHoareMapping(final PrePostConditionSpecification<S> specification, final Map<S, IPredicate> annotation,
			final IPredicate defaultPredicate) {
		mAnnotation = annotation;
		mDefaultPredicate = defaultPredicate;
		mSpecification = specification;
	}

	@Override
	public PrePostConditionSpecification<S> getSpecification() {
		return mSpecification;
	}

	@Override
	public IPredicate getAnnotation(final S state) {
		return mAnnotation.getOrDefault(state, mDefaultPredicate);
	}

	@Override
	public String toString() {
		final var sb = new StringBuilder();
		sb.append("FloydHoareMapping\n----------------------------------------\n");

		final String defaultState = "all other states";

		int stateColumnLength =
				mAnnotation.keySet().stream().map(Object::toString).mapToInt(String::length).max().orElse(0);
		if (mDefaultPredicate != null) {
			stateColumnLength = Integer.max(stateColumnLength, defaultState.length());
		}
		final String format = "%" + stateColumnLength + "s  ::  %s\n";

		for (final var entry : mAnnotation.entrySet()) {
			sb.append(String.format(format, entry.getKey(), entry.getValue()));
		}
		if (mDefaultPredicate != null) {
			sb.append('\n');
			sb.append(String.format(format, defaultState, mDefaultPredicate));
		}

		sb.append("----------------------------------------");
		return sb.toString();
	}
}
