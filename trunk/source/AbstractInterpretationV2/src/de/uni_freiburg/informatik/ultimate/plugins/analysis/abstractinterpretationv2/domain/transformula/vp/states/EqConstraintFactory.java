package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>, 
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
			FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> unfreeze(
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> 
			getDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		return new EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>(constraintList);
	}
	
	
	public EqConstraint<ACTION, NODE, FUNCTION> conjoin(
			List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = getEmptyConstraint();
		
		for (EqConstraint<ACTION, NODE, FUNCTION> conjunct : conjuncts) {
			newConstraint.addNodes(conjunct.getAllNodes());
			
			for (Entry<NODE, NODE> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				newConstraint.merge(eq.getKey(), eq.getValue());
			}
			
			for (VPDomainSymmetricPair<NODE> deq : conjunct.getElementDisequalities()) {
				newConstraint.addRawDisequality(deq.getFirst(), deq.getSecond());
			}
			
			for (Entry<FUNCTION, FUNCTION> aEq : conjunct.getSupportingFunctionEqualities()) {
				newConstraint.addFunctionEquality(aEq.getKey(), aEq.getValue());
			}
			
			for (VPDomainSymmetricPair<FUNCTION> aDeq : conjunct.getFunctionDisequalites()) {
				newConstraint.addFunctionDisequality(aDeq.getFirst(), aDeq.getSecond());
			}

			if (newConstraint.checkForContradiction()) {
				return getBottomConstraint();
			}
		}
		
		newConstraint.freeze();
		return newConstraint;

	}
}
