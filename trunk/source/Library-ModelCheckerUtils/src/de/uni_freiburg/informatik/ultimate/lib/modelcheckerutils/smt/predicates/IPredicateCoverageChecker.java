/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public interface IPredicateCoverageChecker {

	/**
	 * Returns validity of the implication lhs.getFormula() ==> rhs.getFormula().
	 */
	Validity isCovered(IPredicate lhs, IPredicate rhs);

	/**
	 * Returns all known predicates that are covered by the predicate pred (i.e. all predicates that imply pred).
	 */
	Set<IPredicate> getCoveredPredicates(IPredicate pred);

	/**
	 * Returns all known predicates that cover the predicate pred (i.e. all predicates that are implied by pred).
	 */
	Set<IPredicate> getCoveringPredicates(IPredicate pred);

	/**
	 * Get a {@link IPartialComparator} that can compare {@link IPredicate}s that are known to this object. An
	 * {@link IPredicate} p1 is strictly greater (resp. smaller) than an {@link IPredicate} p2 iff p1 represents a set
	 * of states that is strictly greater (resp. smaller) than the set of states that is represented by p2. (E.g, "true"
	 * is strictly greater than "false").
	 */
	IPartialComparator<IPredicate> getPartialComperator();

	/**
	 * @return A relation between predicates where an element (A,B) of the relation means that A implies B and which can
	 *         be freely modified by the caller.
	 */
	HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation();
}
