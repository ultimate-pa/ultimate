package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;


public class DnfTransformer extends TermTransformer {
	
	private final Script m_Script;

	
	
	public DnfTransformer(Script script) {
		super();
		m_Script = script;
	}

	@Override
	protected void convert(Term term) {
		assert term.getSort().getName().equals("Bool");
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term; 
			String functionName = appTerm.getFunction().getName();
			if (functionName.equals("and")) {
				super.convert(term);
				return;
			} else if (functionName.equals("or")) {
				super.convert(term);
				return;
			} else if (functionName.equals("not")) {
				assert appTerm.getParameters().length == 1;
				Term notParam = appTerm.getParameters()[0];
				convertNot(notParam, term);
				return;
			} else if (functionName.equals("=>")) {
				Term[] params = appTerm.getParameters();
				super.convert(Util.or(m_Script, negateAllButLast(params)));
				return;
			} else {
				//consider term as atom
				setResult(term);
				return;
			}
		} else if (term instanceof TermVariable) {
			//consider term as atom
			setResult(term);
		} else if (term instanceof ConstantTerm) {
			//consider term as atom
			setResult(term);
		}else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("quantifer not supported");
		} else {
			throw new UnsupportedOperationException("Unsupported " + term.getClass());
		}
	}
	
	private void convertNot(Term notParam, Term notTerm) {
		assert notParam.getSort().getName().equals("Bool");
		if (notParam instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) notParam; 
			String functionName = appTerm.getFunction().getName();
			Term[] params = appTerm.getParameters();
			if (functionName.equals("and")) {
				super.convert(Util.or(m_Script, negateTerms(params)));
				return;
			} else if (functionName.equals("or")) {
				super.convert(Util.and(m_Script, negateTerms(params)));
				return;
			} else if (functionName.equals("not")) {
				assert appTerm.getParameters().length == 1;
				Term notnotParam = appTerm.getParameters()[0];
				super.convert(notnotParam);
				return;
			} else if (functionName.equals("=>")) {
				super.convert(Util.and(m_Script, negateLast(params)));
				return;
			} else {
				//consider original term as atom
				setResult(notTerm);
				return;
			}
		} else if (notParam instanceof ConstantTerm) {
			//consider term as atom
			setResult(notTerm);
		}else if (notParam instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("quantifer not supported");
		} else {
			throw new UnsupportedOperationException("Unsupported " + notParam.getClass());
		}
	}
	
	private Term[] negateTerms(Term[] terms) {
		Term[] newTerms = new Term[terms.length];
		for (int i=0; i<terms.length; i++) {
			newTerms[i] = Util.not(m_Script, terms[i]);
		}
		return newTerms;
	}
	
	private Term[] negateLast(Term[] terms) {
		Term[] newTerms = new Term[terms.length];
		for (int i=0; i<terms.length-1; i++) {
			newTerms[i] = terms[i];
		}
		newTerms[terms.length-1] = Util.not(m_Script, terms[terms.length-1]);
		return newTerms;
	}
	
	private Term[] negateAllButLast(Term[] terms) {
		Term[] newTerms = new Term[terms.length];
		for (int i=0; i<terms.length-1; i++) {
			newTerms[i] = Util.not(m_Script, terms[i]);
		}
		newTerms[terms.length-1] = terms[terms.length-1];
		return newTerms;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		String functionSymbolName = appTerm.getFunction().getName();
		Term result;
		if (functionSymbolName.equals("and")) {
			HashSet<Term> disjuncts = new HashSet<Term>();
			disjuncts.add(m_Script.term("true"));
			HashSet<Term> oldDisjuncts;
			for (Term conjunct : newArgs) {
				oldDisjuncts = disjuncts;
				disjuncts = new HashSet<Term>();
				if ((conjunct instanceof ApplicationTerm) && 
						((ApplicationTerm) conjunct).getFunction().getName().equals("or")) {
					Term[] atoms = ((ApplicationTerm) conjunct).getParameters();
					for (Term atom : atoms) {
						for (Term disjunct : oldDisjuncts) {
							disjuncts.add(Util.and(m_Script, disjunct, atom));
						}

					}
					
				} else {
					for (Term disjunct : oldDisjuncts) {
						disjuncts.add(Util.and(m_Script, disjunct, conjunct));
					}
				}
			}
			result = Util.or(m_Script, disjuncts.toArray(new Term[0]));
		} else if (functionSymbolName.equals("or")) {
			result = Util.or(m_Script, newArgs);
		} else {
			throw new AssertionError();
		}
		setResult(result);
	}

}
