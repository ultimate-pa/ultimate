package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IDomainSpecificOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqOperationProvider<ACTION extends IIcfgTransition<IcfgLocation>> implements 
 		IDomainSpecificOperationProvider<EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst>, EqPredicate, EqTransitionRelation> {
	
	EqConstraintFactory<ACTION, EqNode, IProgramVarOrConst> mEqConstraintFactory;

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> getConstraint(EqPredicate p) {
		return p.getEqConstraint();
	}

	@Override
	public boolean isConstaintUnsatisfiable(EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		return constraint.isBottom();
	}

	@Override
	public boolean isConstaintValid(EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> getConstaintFromTransitionRelation(
			EqTransitionRelation transRel) {
		return transRel.getEqConstraint();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> renameVariables(Map<Term, Term> substitutionMapping,
			EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		final EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> newConstraint =	
				mEqConstraintFactory.unfreeze(constraint);
		newConstraint.renameVariables(substitutionMapping);
		newConstraint.freeze();
		return newConstraint;
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constructConjunction(
			List<EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst>> conjuncts) {
		// TODO
		return null;
	}
	
	
	public EqConstraint<ACTION, EqNode, IProgramVarOrConst> conjoin(
			List<EqConstraint<ACTION, EqNode, IProgramVarOrConst>> conjuncts) {
		final EqConstraint<ACTION, EqNode, IProgramVarOrConst> newConstraint = mEqConstraintFactory.getEmptyConstraint();
		
		for (EqConstraint<ACTION, EqNode, IProgramVarOrConst> conjunct : conjuncts) {
			newConstraint.addNodes(conjunct.getAllNodes());
			
			for (Entry<EqNode, EqNode> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				newConstraint.merge(eq.getKey(), eq.getValue());
			}
			
			for (VPDomainSymmetricPair<EqNode> deq : conjunct.getElementDisequalities()) {
				newConstraint.addRawDisequality(deq.getFirst(), deq.getSecond());
			}
			
			for (Entry<IProgramVarOrConst, IProgramVarOrConst> aEq : conjunct.getSupportingFunctionEqualities()) {
				newConstraint.addFunctionEquality(aEq.getKey(), aEq.getValue());
			}
			
			for (VPDomainSymmetricPair<IProgramVarOrConst> aDeq : conjunct.getFunctionDisequalites()) {
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
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> projectExistentially(Set<TermVariable> varsToProjectAway,
			EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		final EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> newConstraint =	
				mEqConstraintFactory.unfreeze(constraint);
		newConstraint.projectExistentially(varsToProjectAway);
		newConstraint.freeze();
		return newConstraint;
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constructDisjunction(
			List<EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst>> disjuncts) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constructNegation(
			EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> operand) {
		throw new UnsupportedOperationException();
	}

	@Override
	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> projectUniversally(Set<TermVariable> varsToProjectAway,
			EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		throw new UnsupportedOperationException();
	}

}
