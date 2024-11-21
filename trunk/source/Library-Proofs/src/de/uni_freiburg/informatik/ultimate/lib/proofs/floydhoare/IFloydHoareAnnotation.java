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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProof;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;

/**
 * A Floyd/Hoare annotation of a program, which is usually represented as some kind of graph (e.g. ICFG or automaton).
 * The annotation labels nodes of this graph (called "states") with {@link IPredicate}s.
 *
 * Floyd/Hoare annotations prove {@link PrePostConditionSpecification}s. A valid annotation satisfies the following
 * criteria:
 * <ol>
 * <li>The initial states (as identified by the specification) are labeled by a predicate which is entailed by the
 * specification's precondition.</li>
 * <li>For every edge, the annotation of the source state, the label of the edge and the annotation of the target state
 * form a valid Hoare triple.</li>
 * <li>Every final state (according to the specification) is labeled by a predicate that entails the specification's
 * postcondition.</li>
 * </ol>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            the type of states
 */
public interface IFloydHoareAnnotation<S> extends IProof {
	/**
	 * The pre-/postcondition specification proven by this instance.
	 */
	@Override
	PrePostConditionSpecification<S> getSpecification();

	/**
	 * Retrieves the predicate annotating the given state.
	 *
	 * This method may return {@code null} if no annotation for the given state is known. Note that this is different
	 * from returning {@code true}: If the state is labeled with {@code true}, all outgoing edges whose target node has
	 * an annotation must correspond to a valid Hoare triple with the precondition {@code true}, otherwise we consider
	 * the annotation invalid. If the state does not have an annotation (i.e., {@code null} is returned), there are no
	 * Hoare triples for the outgoing edges that are required to be valid.
	 *
	 * @param state
	 *            a state (control location) of the program
	 * @return the predicate labeling the given state
	 */
	IPredicate getAnnotation(S state);
}
