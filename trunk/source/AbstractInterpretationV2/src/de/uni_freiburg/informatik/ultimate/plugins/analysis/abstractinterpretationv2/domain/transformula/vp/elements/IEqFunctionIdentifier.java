package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;

public interface IEqFunctionIdentifier<NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
	FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	FUNCTION renameVariables(Map<Term, Term> substitutionMapping);
	
	int getArity();
	
	Term getTerm();
	
	boolean dependsOn(FUNCTION f);
	
	boolean isStore();
	
	FUNCTION getFunction();
	
	List<NODE> getStoreIndices();

	NODE getValue();

	FUNCTION getInnerMostFunction();
}
