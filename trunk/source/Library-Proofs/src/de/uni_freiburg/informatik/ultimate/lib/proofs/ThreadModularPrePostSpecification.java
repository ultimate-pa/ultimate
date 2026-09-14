/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs;

import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A special kind of {@link PrePostConditionSpecification} for concurrent programs, which considers a configuration (or
 * "marking", in Petri net terminology) of the concurrent program to be accepting if any thread is in an accepting
 * location (or "place", in Petri net terminology).
 *
 * @param <P>
 *            The type of places resp. locations of individual threads
 * @param <M>
 *            The type of "markings", i.e., control configurations of the entire concurrent program
 */
public class ThreadModularPrePostSpecification<P, M extends Iterable<P>> extends PrePostConditionSpecification<M> {
	private final Predicate<P> mIsFinalThreadState;

	public ThreadModularPrePostSpecification(final Map<M, IPredicate> initialStates,
			final Predicate<P> isFinalThreadState, final IPredicate postcondition) {
		super(initialStates, isFinalState(isFinalThreadState), postcondition);
		mIsFinalThreadState = isFinalThreadState;
	}

	public boolean isFinalThreadState(final P place) {
		return mIsFinalThreadState.test(place);
	}

	private static <P, M extends Iterable<P>> Predicate<M> isFinalState(final Predicate<P> isFinalThreadState) {
		return m -> StreamSupport.stream(m.spliterator(), false).anyMatch(isFinalThreadState);
	}
}
