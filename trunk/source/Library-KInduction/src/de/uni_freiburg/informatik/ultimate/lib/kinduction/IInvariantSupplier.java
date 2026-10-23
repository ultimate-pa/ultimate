/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Extension point for an independent, CEGAR-agnostic analysis that can supply a loop invariant to strengthen
 * {@link KInduction}'s inductive step. A supplied invariant is used purely as a hypothesis (never re-proven by
 * {@link KInduction} itself), so it must already be sound on its own - a genuine over-approximation of every state
 * reachable at {@code loopHead}, e.g. as computed by an abstract-interpretation-style analysis. Assuming a sound
 * invariant can only prune the step-case search space (letting a smaller {@code k} become inductive); it can never
 * introduce unsoundness.
 *
 * @param <STATE>
 *            the automaton state type identifying a loop head, matching {@link KInduction}'s own {@code STATE}.
 */
public interface IInvariantSupplier<STATE> {

	/**
	 * @param loopHead
	 *            the loop head to supply an invariant for.
	 * @param targetScript
	 *            the {@link ManagedScript} the returned {@link Term} must already be native to (no cross-script
	 *            transfer is performed by the caller).
	 * @return a state predicate over {@code loopHead}'s own {@code IProgramVar}s, known to hold whenever control
	 *         reaches {@code loopHead}, or {@link Optional#empty()} if none is available.
	 */
	Optional<Term> getInvariant(STATE loopHead, ManagedScript targetScript);

	/**
	 * Takes whatever the supplier has learned since the last call, without waiting. {@link #getInvariant} answers from
	 * what was taken so far. A supplier whose invariants never change has nothing to take.
	 *
	 * @return true if some invariant may have changed since the last call
	 */
	default boolean update() {
		return false;
	}

	/**
	 * Called by k-induction when it starts to ask a query, with the invariants taken by the last {@link #update()}.
	 */
	default void queryStarted(final KInductionQuery.Kind kind, final int k) {
		// nothing to watch
	}

	/**
	 * Called by k-induction when a query was answered or interrupted.
	 *
	 * @param millis
	 *            how long the query took
	 */
	default void queryFinished(final KInductionQuery.Kind kind, final int k, final long millis) {
		// nothing to watch
	}

	/**
	 * @return whether the supplier may interrupt the queries of k-induction; then k-induction registers an interrupter
	 *         with {@link #setInterrupter}
	 */
	default boolean mayInterrupt() {
		return false;
	}

	/**
	 * Called by k-induction once, if the supplier {@link #mayInterrupt()}.
	 *
	 * @param interrupter
	 *            interrupts the running query, from any thread, and says whether one was running; k-induction then
	 *            takes what the supplier published and the supplier's answer, see {@link #takeAnswer}
	 */
	default void setInterrupter(final BooleanSupplier interrupter) {
		// never interrupts
	}

	/**
	 * Called by k-induction after the supplier interrupted a query.
	 *
	 * @return the answer the supplier's probe found for this query, with weaker invariants, if it probed it
	 */
	default Optional<LBool> takeAnswer(final KInductionQuery.Kind kind, final int k) {
		return Optional.empty();
	}

	/**
	 * @return a supplier that never provides an invariant, i.e. plain (unstrengthened) k-induction.
	 */
	static <STATE> IInvariantSupplier<STATE> none() {
		return (loopHead, targetScript) -> Optional.empty();
	}

	/**
	 * @param invariants
	 *            invariants over the loop heads' own {@code IProgramVar}s, native to {@code script}
	 * @param script
	 *            the {@link ManagedScript} the invariants are native to
	 * @return a supplier that returns the given invariants, and none for other loop heads or for another script.
	 */
	static <STATE> IInvariantSupplier<STATE> fromMap(final java.util.Map<STATE, Term> invariants,
			final ManagedScript script) {
		return (loopHead, targetScript) -> targetScript == script ? Optional.ofNullable(invariants.get(loopHead))
				: Optional.empty();
	}
}
