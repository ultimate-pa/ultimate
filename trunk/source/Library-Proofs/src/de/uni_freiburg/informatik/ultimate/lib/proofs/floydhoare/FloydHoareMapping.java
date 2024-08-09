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
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * A simple implementation of {@link IFloydHoareAnnotation} backed by a map.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            the type of states which are annotated
 */
public class FloydHoareMapping<S> implements IFloydHoareAnnotation<S> {
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final Map<S, IPredicate> mAnnotation;

	private final IPredicate mDefaultPredicate;

	public FloydHoareMapping(final IPredicateUnifier unifier, final Map<S, IPredicate> annotation) {
		this(unifier, annotation, null);
	}

	public FloydHoareMapping(final IPredicateUnifier unifier, final Map<S, IPredicate> annotation,
			final IPredicate defaultPredicate) {
		this(unifier.getTruePredicate(), unifier.getFalsePredicate(), annotation, defaultPredicate);
	}

	public FloydHoareMapping(final IPredicate precondition, final IPredicate postcondition,
			final Map<S, IPredicate> annotation) {
		this(precondition, postcondition, annotation, null);
	}

	/**
	 *
	 * @param precondition
	 * @param postcondition
	 * @param annotation
	 *            the underlying map from states to their annotations
	 * @param defaultPredicate
	 *            A default predicate to be returned when no annotation for a given state is known.
	 */
	public FloydHoareMapping(final IPredicate precondition, final IPredicate postcondition,
			final Map<S, IPredicate> annotation, final IPredicate defaultPredicate) {
		mPrecondition = Objects.requireNonNull(precondition);
		mPostcondition = Objects.requireNonNull(postcondition);
		mAnnotation = annotation;
		mDefaultPredicate = defaultPredicate;
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public IPredicate getAnnotation(final S state) {
		return mAnnotation.getOrDefault(state, mDefaultPredicate);
	}
}
