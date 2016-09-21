package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqNode {
	
	public Term term;
	
	public EqNode(Term term) {
		this.term = term;
	}
	
	public String toString() {
		return term.toString();
		
	}
}
