/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IDomainSpecificOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqOperationProvider implements
 		IDomainSpecificOperationProvider<
 			EqDisjunctiveConstraint<EqNode>,
 			EqPredicate,
 			EqTransitionRelation> {

	private final EqConstraintFactory<EqNode> mEqConstraintFactory;

	public EqOperationProvider(final EqConstraintFactory<EqNode> eqConstraintFactory) {
		mEqConstraintFactory = eqConstraintFactory;
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> getConstraint(final EqPredicate p) {
		return p.getEqConstraint();
	}

	@Override
	public boolean isConstraintUnsatisfiable(final EqDisjunctiveConstraint<EqNode> constraint) {
		return constraint.isBottom();
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> getConstraintFromTransitionRelation(
			final EqTransitionRelation transRel) {
		return transRel.getEqConstraint();
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> renameVariables(
			final Map<Term, Term> substitutionMapping,
			final EqDisjunctiveConstraint<EqNode> constraint) {
//		return constraint.renameVariables(substitutionMapping);
		return mEqConstraintFactory.renameVariables(constraint, substitutionMapping);
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> constructConjunction(
			final List<EqDisjunctiveConstraint<EqNode>> conjuncts) {
		return mEqConstraintFactory.conjoinDisjunctiveConstraints(conjuncts);
	}




	@Override
	public EqDisjunctiveConstraint<EqNode> projectExistentially(final Set<TermVariable> varsToProjectAway,
			final EqDisjunctiveConstraint<EqNode> constraint) {
		final Set<Term> castToSetOfTerm = varsToProjectAway.stream().map(tv -> (Term) tv).collect(Collectors.toSet());
		return constraint.projectExistentially(castToSetOfTerm);
	}


	@Override
	public boolean isConstraintValid(final EqDisjunctiveConstraint<EqNode> constraint) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> constructDisjunction(
			final List<EqDisjunctiveConstraint<EqNode>> disjuncts) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> constructNegation(
			final EqDisjunctiveConstraint<EqNode> operand) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<EqNode> projectUniversally(final Set<TermVariable> varsToProjectAway,
			final EqDisjunctiveConstraint<EqNode> constraint) {
		throw new UnsupportedOperationException();
	}


}
