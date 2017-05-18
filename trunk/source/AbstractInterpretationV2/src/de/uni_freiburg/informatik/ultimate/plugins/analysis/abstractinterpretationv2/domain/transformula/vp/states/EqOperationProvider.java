package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IDomainSpecificOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqOperationProvider<ACTION extends IIcfgTransition<IcfgLocation>> implements 
 		IDomainSpecificOperationProvider<
 			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>, 
 			EqPredicate<ACTION>, 
 			EqTransitionRelation<ACTION>> {
	
	EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getConstraint(EqPredicate<ACTION> p) {
		return p.getEqConstraint();
	}

	@Override
	public boolean isConstaintUnsatisfiable(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		return constraint.isBottom();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getConstaintFromTransitionRelation(
			EqTransitionRelation<ACTION> transRel) {
		return transRel.getEqConstraint();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> renameVariables(
			Map<Term, Term> substitutionMapping,
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		return constraint.renameVariables(substitutionMapping);
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constructConjunction(
			List<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> conjuncts) {
		
		final List<Set<EqConstraint<ACTION, EqNode, EqFunction>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());
		
		final Set<List<EqConstraint<ACTION, EqNode, EqFunction>>> crossProduct = 
				VPDomainHelpers.computeCrossProduct(listOfConstraintSets);
		
		final Set<EqConstraint<ACTION, EqNode, EqFunction>> constraintSet = crossProduct.stream()
				.map(constraintList -> mEqConstraintFactory.conjoin(constraintList))
				.collect(Collectors.toSet());

		return mEqConstraintFactory.getDisjunctiveConstraint(constraintSet);
	}
	
	


	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> projectExistentially(Set<TermVariable> varsToProjectAway,
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		return constraint.projectExistentially(varsToProjectAway);
	}


	@Override
	public boolean isConstaintValid(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constructDisjunction(
			List<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> disjuncts) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constructNegation(
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> operand) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> projectUniversally(Set<TermVariable> varsToProjectAway,
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		throw new UnsupportedOperationException();
	}


}
