/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

/**
 * An {@link IEmpire} with direct access to reachable states, as well as incoming and outgoing edges of each state.
 *
 * Use {@link EmpireReachableStates} to turn an arbitrary {@link IEmpire} into an instance of this interface.
 *
 * @param <L>
 *            the type of letters in the Petri program
 * @param <P>
 *            the type of places in the Petri program
 * @param <S>
 *            the type of states in the empire
 */
public interface IExplicitEmpire<L, P, S> extends IEmpire<L, P, S>, INestedWordAutomaton<Transition<L, P>, S> {

	/**
	 * @deprecated We should not abuse the final states for empires, they do not represent any meaningful language.
	 *             Instead introduce a suitably-named new method.
	 */
	@Override
	@Deprecated
	Collection<S> getFinalStates();

	@Deprecated
	@Override
	default Set<Transition<L, P>> lettersReturn(final S state) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Set<Transition<L, P>> lettersSummary(final S state) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Set<Transition<L, P>> lettersCallIncoming(final S state) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Set<Transition<L, P>> lettersReturnIncoming(final S state) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<IncomingCallTransition<Transition<L, P>, S>> callPredecessors(final S succ,
			final Transition<L, P> letter) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<IncomingCallTransition<Transition<L, P>, S>> callPredecessors(final S succ) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<IncomingReturnTransition<Transition<L, P>, S>> returnPredecessors(final S succ, final S hier,
			final Transition<L, P> letter) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<IncomingReturnTransition<Transition<L, P>, S>> returnPredecessors(final S succ,
			final Transition<L, P> letter) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<IncomingReturnTransition<Transition<L, P>, S>> returnPredecessors(final S succ) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<OutgoingReturnTransition<Transition<L, P>, S>> returnSuccessors(final S state) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<SummaryReturnTransition<Transition<L, P>, S>> summarySuccessors(final S hier,
			final Transition<L, P> letter) {
		return Collections.emptySet();
	}

	@Deprecated
	@Override
	default Iterable<SummaryReturnTransition<Transition<L, P>, S>> summarySuccessors(final S hier) {
		return Collections.emptySet();
	}
}
