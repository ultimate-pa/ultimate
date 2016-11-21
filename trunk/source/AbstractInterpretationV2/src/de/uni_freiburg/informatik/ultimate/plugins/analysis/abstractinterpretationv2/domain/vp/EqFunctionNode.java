package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqFunctionNode extends EqNode {
	
	private final Term function;
	private final EqNode arg;

	public EqFunctionNode(Term term, Term function, EqNode arg) {
		super(term);
		this.function = function;
		this.arg = arg;
	}
	
	public Term getFunction() {
		return function;
	}

	public EqNode getArg() {
		return arg;
	}

	public String toString() {
		return function.toString() + "[" + arg.toString() + "]";
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof EqFunctionNode)) {
			return false;
		}
		return term.equals(((EqFunctionNode)o).getTerm()) && arg.getTerm().equals((((EqFunctionNode)o).getArg()).getTerm());
	}
	
}
