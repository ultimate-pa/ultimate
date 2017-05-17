package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface IEqFunctionIdentifier<FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {

	public FUNCTION renameVariables(Map<Term, Term> substitutionMapping);
}
