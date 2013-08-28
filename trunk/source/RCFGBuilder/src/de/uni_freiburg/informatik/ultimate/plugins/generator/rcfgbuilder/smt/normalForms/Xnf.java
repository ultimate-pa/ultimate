package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Common abstract superclass of Cnf and Dnf. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class Xnf extends Nnf {

	public Xnf(Script script) {
		super(script);
	}
	
	protected abstract class XnfTransformerHelper extends NnfTransformerHelper {

		public abstract String innerConnectiveSymbol();
		public abstract String outerConnectiveSymbol();
		
		public abstract String innerConnectiveNeutralElement();
		
		public abstract Term innerConnective(Script script, Term... params);
		public abstract Term outerConnective(Script script, Term... params);
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String functionSymbolName = appTerm.getFunction().getName();
			Term result;
			if (functionSymbolName.equals(innerConnectiveSymbol())) {
				HashSet<Term> outerTerms = new HashSet<Term>();
				outerTerms.add(m_Script.term(innerConnectiveNeutralElement()));
				HashSet<Term> oldOuterTerms;
				for (Term inner : newArgs) {
					oldOuterTerms = outerTerms;
					outerTerms = new HashSet<Term>();
					if ((inner instanceof ApplicationTerm) && 
							((ApplicationTerm) inner).getFunction().getName().equals(outerConnectiveSymbol())) {
						Term[] atoms = ((ApplicationTerm) inner).getParameters();
						for (Term atom : atoms) {
							for (Term oldOuter : oldOuterTerms) {
								outerTerms.add(innerConnective(m_Script, oldOuter, atom));
							}
						}
					} else {
						for (Term oldOuter : oldOuterTerms) {
							outerTerms.add(innerConnective(m_Script, oldOuter, inner));
						}
					}
				}
				result = outerConnective(m_Script, outerTerms.toArray(new Term[0]));
			} else if (functionSymbolName.equals(outerConnectiveSymbol())) {
				result = outerConnective(m_Script, newArgs);
			} else {
				throw new AssertionError();
			}
			setResult(result);
		}

	}

}
