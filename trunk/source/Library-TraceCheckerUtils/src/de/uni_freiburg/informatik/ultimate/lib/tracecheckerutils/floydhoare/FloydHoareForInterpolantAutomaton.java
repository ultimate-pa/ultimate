/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

public class FloydHoareForInterpolantAutomaton<L extends IAction> implements IFloydHoareAnnotation<L, IPredicate> {
	private final INwaOutgoingTransitionProvider<L, IPredicate> mInterpolantAutomaton;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;

	public FloydHoareForInterpolantAutomaton(final INwaOutgoingTransitionProvider<L, IPredicate> interpolantAutomaton,
			final IPredicateUnifier unifier) {
		this(interpolantAutomaton, unifier.getTruePredicate(), unifier.getFalsePredicate());
	}

	public FloydHoareForInterpolantAutomaton(final INwaOutgoingTransitionProvider<L, IPredicate> interpolantAutomaton,
			final IPredicate precondition, final IPredicate postcondition) {
		mInterpolantAutomaton = interpolantAutomaton;
		mPrecondition = precondition;
		mPostcondition = postcondition;
	}

	@Override
	public INwaOutgoingTransitionProvider<L, IPredicate> getAnnotatedAutomaton() {
		return mInterpolantAutomaton;
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
	public IPredicate getAnnotation(final IPredicate state) {
		return state;
	}
}
