package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqBaseNode extends EqNode {

	EqNode representative;
	
	public EqBaseNode(Term term) {
		super(term);
	}
	
	public String toString() {
		return "Base Node: " + term.toString();
		
	}
	
}
