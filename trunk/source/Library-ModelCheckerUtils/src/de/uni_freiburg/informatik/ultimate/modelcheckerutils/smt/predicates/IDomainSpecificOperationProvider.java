/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ITransitionRelation;

/**
 * Provides operations for {@link PredicateTransformer}
 * TODO: extend to WP operations
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IDomainSpecificOperationProvider<C,P extends IAbstractPredicate, R extends ITransitionRelation> {

	C getConstraint(P p);

	/**
	 * This operation is needed for post but not for wp.
	 * 
	 * @return true if provider can guarantee that constraint is unsatisfiable
	 *         (i.e., equivalent to false, resp. the empty set of program
	 *         states) It is always safe to return false here, the true return
	 *         value can only bring some speedup.
	 * 
	 */
	boolean isConstraintUnsatisfiable(C constraint);

	/**
	 * This operation is needed for wp but not for post.
	 * 
	 * @return true if provider can guarantee that constraint is valid (i.e.,
	 *         equivalent to true, resp. the set of all program states) It is
	 *         always safe to return false here, the true return value can only
	 *         bring some speedup.
	 * 
	 */
	boolean isConstraintValid(C constraint);

	C getConstraintFromTransitionRelation(R transRel);

	/**
	 * @param substitutionMapping
	 *            maps old variables to new variables
	 */
	C renameVariables(Map<Term, Term> substitutionMapping, C constraint);

	/**
	 * This operation is needed for post but not for wp.
	 */
	C constructConjunction(List<C> conjuncts);

	/**
	 * This operation is needed for wp but not for post.
	 */
	C constructDisjunction(List<C> disjuncts);

	/**
	 * This operation is needed for wp but not for post.
	 */
	C constructNegation(C operand);

	/**
	 * Project constraint to all program vars that are not in the set
	 * varsToProjectAway. The projection is an existential projection. This
	 * operation is needed for post but not for wp.
	 */
	C projectExistentially(Set<TermVariable> varsToProjectAway, C constraint);

	/**
	 * Project constraint to all program vars that are not in the set
	 * varsToProjectAway. The projection is a universal projection. This
	 * operation is needed for wp but not for post.
	 */
	C projectUniversally(Set<TermVariable> varsToProjectAway, C constraint);

}