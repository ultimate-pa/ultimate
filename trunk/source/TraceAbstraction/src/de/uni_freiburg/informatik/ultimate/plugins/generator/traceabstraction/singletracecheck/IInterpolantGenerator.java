/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.Arrays;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * Interface for objects that generate sequences of interpolants. Given
 * <ul>
 * <li>a precondition stated by predicate φ_0
 * <li>a postcondition stated by predicate φ_n
 * <li>a trace (which is a word of CodeBlocks) cb_0 cb_1 ... cb_{n-1},
 * </ul>
 * a sequence of interpolants is a sequence of predicates φ_1,...,φ_{n-1} such that the inclusion post(φ_i, cb_i}) ⊆
 * φ_{i+1} holds for 0⩽i<n. A sequence of interpolants can be seen as a Hoare annotation for the program that
 * corresponds to the trace.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public interface IInterpolantGenerator {

	Word<? extends IAction> getTrace();

	IPredicate getPrecondition();

	IPredicate getPostcondition();

	Map<Integer, IPredicate> getPendingContexts();

	/**
	 * @return A sequence of predicates that is a sequence of interpolations according to the definition given above.
	 */
	IPredicate[] getInterpolants();

	/**
	 * @return The PredicateUnifier that was used to construct the interpolants.
	 */
	IPredicateUnifier getPredicateUnifier();

	default TracePredicates getIpp() {
		return new TracePredicates(getPrecondition(), getPostcondition(),
				Arrays.asList(getInterpolants()));
	}

	/**
	 * @return {@code true} iff the interpolant sequence is perfect.
	 */
	boolean isPerfectSequence();

	/**
	 * @return {@code true} iff the {@link IInterpolantGenerator} returns a usable interpolant sequence even if it is
	 *         imperfect. Certain interpolant generators (e.g. CegarAbsIntRunner in TraceAbstraction) can only deliver
	 *         perfect sequences.
	 * @deprecated This method is necessary as long as the trace checking / interpolant generation architecture is not
	 *             refactored to accommodate algorithms that may produce invariants that are too weak
	 */
	@Deprecated
	default boolean imperfectSequencesUsable() {
		return true;
	}

	InterpolantComputationStatus getInterpolantComputationStatus();
}
