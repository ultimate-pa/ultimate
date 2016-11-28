package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class PointerExpression {
	
	private Term term;
	private Map<TermVariable, IProgramVar> termMap;
	private boolean isConstant;
	
	public PointerExpression (Term term, Map<TermVariable, IProgramVar> termMap) {
		this.term = term;
		this.termMap = new HashMap<TermVariable, IProgramVar>(termMap);
		isConstant = false;
	}
	
	public PointerExpression (Term term, boolean isConstant) {
		this.term = term;
		termMap = null;
		this.isConstant = isConstant;
	}
	
	public Term getTerm() {
		return term;
	}
	public void setTerm(Term term) {
		this.term = term;
	}
	
	public Map<TermVariable, IProgramVar> getTermMap() {
		return termMap;
	}
	public void setTermMap(Map<TermVariable, IProgramVar> termMap) {
		this.termMap = termMap;
	}

	public boolean isConstant() {
		return isConstant;
	}

	public void setConstant(boolean isConstant) {
		this.isConstant = isConstant;
	}
	
	@Override
	public String toString() {
		return "Term: " + getTerm().toString();
	}
	
}
