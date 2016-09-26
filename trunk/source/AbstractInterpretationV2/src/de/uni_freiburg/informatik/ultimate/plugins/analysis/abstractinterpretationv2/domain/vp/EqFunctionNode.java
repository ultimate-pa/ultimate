package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqFunctionNode extends EqNode {
	
	public EqNode arg;

	public EqFunctionNode(Term function, EqNode arg) {
		super(function);
		this.arg = arg;
	}
	
	public EqNode getArg() {
		return arg;
	}

	public void setArg(EqNode arg) {
		this.arg = arg;
	}
	
	public String toString() {
		return term.toString() + "[" + arg + "]";
	}
	
}
