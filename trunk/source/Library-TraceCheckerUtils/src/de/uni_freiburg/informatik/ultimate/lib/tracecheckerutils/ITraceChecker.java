/*
 * Copyright (C) 2023 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Trace Checker which checks whether a run fulfills a given precondition/postcondition pair. The meaning of "fulfills"
 * needs to be decided by the implementation.
 *
 * TODO (Dominik 2024-09-24): What possibly different notions of "fulfilling" (or "satisfying") a
 * precondition/postcondition pair could there be?!
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
// TODO We need to figure out how to appropriately use the existing trace checks (with different strategies, etc.)
public interface ITraceChecker<L> {
	// TODO Why is the run needed, as opposed to just the trace? Which automaton does the run belong to?
	/**
	 * Checks whether the given run fulfills the given precondition/postcondition pair.
	 * 
	 * @param run
	 * @param precondition
	 * @param postcondition
	 * @return
	 */
	public TracePredicates checkTrace(IRun<L, IPredicate> run, IPredicate precondition, IPredicate postcondition);

	/**
	 * Allows to detect successful but imperfect proofs
	 * 
	 * @return true if the trace check was imperfect
	 */
	public boolean wasImperfectProof();
}
