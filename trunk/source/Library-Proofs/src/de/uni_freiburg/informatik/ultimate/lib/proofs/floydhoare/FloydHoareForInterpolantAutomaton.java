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

import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;

/**
 * Represents the Floyd-Hoare automaton for an interpolant automaton, i.e., an automaton whose states are themselves
 * predicates that form an inductive annotation.
 *
 * Hence, an instance of this class does not actually carry any information and is only used in order to provide a
 * common interface when an {@link IFloydHoareAnnotation} is needed, e.g. for {@link FloydHoareValidityCheck}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class FloydHoareForInterpolantAutomaton implements IFloydHoareAnnotation<IPredicate> {
	private final PrePostConditionSpecification<IPredicate> mSpec;

	/**
	 * Create an instance with the default specification.
	 *
	 * @param unifier
	 *            A predicate unifier used to retrieve predicates representing pre- and postcondition
	 */
	public FloydHoareForInterpolantAutomaton(final IPredicateUnifier unifier,
			final INwaOutgoingTransitionProvider<?, IPredicate> automaton) {
		this(unifier.getTruePredicate(), unifier.getFalsePredicate(), automaton);
	}

	public FloydHoareForInterpolantAutomaton(final IPredicate precondition, final IPredicate postcondition,
			final INwaOutgoingTransitionProvider<?, IPredicate> automaton) {
		this(new PrePostConditionSpecification<>(StreamSupport.stream(automaton.getInitialStates().spliterator(), false)
				.collect(Collectors.toMap(Function.identity(), s -> precondition)), automaton::isFinal, postcondition));
	}

	public FloydHoareForInterpolantAutomaton(final PrePostConditionSpecification<IPredicate> specification) {
		mSpec = specification;
	}

	@Override
	public PrePostConditionSpecification<IPredicate> getSpecification() {
		return mSpec;
	}

	@Override
	public IPredicate getAnnotation(final IPredicate state) {
		return state;
	}
}
