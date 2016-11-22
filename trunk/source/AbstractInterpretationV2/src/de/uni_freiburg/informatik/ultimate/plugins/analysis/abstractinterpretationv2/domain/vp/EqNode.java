package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public abstract class EqNode {
	
//	protected final Term term;
//	
//	/**
//	 * same as term except that every TermVariable is replaced by its default constant
//	 * according to Boogie2SMT
//	 */
//	protected final Term termWithDefaultConstants;
	
//	public EqNode(Term term, Term termWithDefaultConstants) {
//		this.term = term;
//		this.termWithDefaultConstants = termWithDefaultConstants;
//	}
	
//	public String toString() {
//		return term.toString();	
//	}
//	
//	@Override
//	public boolean equals(Object o) {
//		if (!(o instanceof EqNode)) {
//			return false;
//		}
//		return term.equals(((EqNode)o).term);
//	}
//	
//	public Term getTerm() {
//		return term;
//	}
//	
//	public Term getTermWithDefaultConstants() {
//		return termWithDefaultConstants;
//	}
	
	public abstract Term getTerm(Script s) ;
		

}
