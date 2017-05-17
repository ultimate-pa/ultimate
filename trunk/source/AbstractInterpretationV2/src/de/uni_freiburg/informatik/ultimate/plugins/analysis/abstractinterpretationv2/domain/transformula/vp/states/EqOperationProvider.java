package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IDomainSpecificOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
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
		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> newConstraint =	
				mEqConstraintFactory.unfreeze(constraint);
		newConstraint.renameVariables(substitutionMapping);
		newConstraint.freeze();
		return newConstraint;
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constructConjunction(
			List<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> conjuncts) {
		
		final List<Set<EqConstraint<ACTION, EqNode, EqFunction>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());
		
		final Set<List<EqConstraint<ACTION, EqNode, EqFunction>>> crossProduct = 
				VPDomainHelpers.computeCrossProduct(listOfConstraintSets);
		
		final Set<EqConstraint<ACTION, EqNode, EqFunction>> constraintSet = crossProduct.stream()
				.map(constraintList -> conjoin(constraintList))
				.collect(Collectors.toSet());

		return mEqConstraintFactory.getDisjunctiveConstraint(constraintSet);
	}
	
	
	public EqConstraint<ACTION, EqNode, EqFunction> conjoin(
			List<EqConstraint<ACTION, EqNode, EqFunction>> conjuncts) {
		final EqConstraint<ACTION, EqNode, EqFunction> newConstraint = mEqConstraintFactory.getEmptyConstraint();
		
		for (EqConstraint<ACTION, EqNode, EqFunction> conjunct : conjuncts) {
			newConstraint.addNodes(conjunct.getAllNodes());
			
			for (Entry<EqNode, EqNode> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				newConstraint.merge(eq.getKey(), eq.getValue());
			}
			
			for (VPDomainSymmetricPair<EqNode> deq : conjunct.getElementDisequalities()) {
				newConstraint.addRawDisequality(deq.getFirst(), deq.getSecond());
			}
			
			for (Entry<EqFunction, EqFunction> aEq : conjunct.getSupportingFunctionEqualities()) {
				newConstraint.addFunctionEquality(aEq.getKey(), aEq.getValue());
			}
			
			for (VPDomainSymmetricPair<EqFunction> aDeq : conjunct.getFunctionDisequalites()) {
				newConstraint.addFunctionDisequality(aDeq.getFirst(), aDeq.getSecond());
			}

			if (newConstraint.checkForContradiction()) {
				return mEqConstraintFactory.getBottomConstraint();
			}
		}
		
		newConstraint.freeze();
		return newConstraint;

	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> projectExistentially(Set<TermVariable> varsToProjectAway,
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> newConstraint =	
				mEqConstraintFactory.unfreeze(constraint);
		newConstraint.projectExistentially(varsToProjectAway);
		newConstraint.freeze();
		return newConstraint;
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
