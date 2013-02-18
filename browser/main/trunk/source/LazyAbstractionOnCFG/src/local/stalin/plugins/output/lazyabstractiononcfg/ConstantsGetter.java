package local.stalin.plugins.output.lazyabstractiononcfg;

import java.util.HashSet;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.DistinctAtom;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.FletFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.LetFormula;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.ProgramVariableTerm;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.RationalTerm;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.VariableAtom;
import local.stalin.logic.VariableTerm;

public class ConstantsGetter {

	// -------------------------------------------------------------------------
	//------------------------ formula walking stuff ---------------------------
	// -------------------------------------------------------------------------
	
//	private HashSet<TermVariable> getFreeVariables(Formula f) {
//		return getFreeVariables(f, new HashSet<TermVariable>());
//	}
//	private HashSet<TermVariable> getFreeVariables(Term t) {
//		return getFreeVariables(t, new HashSet<TermVariable>());
//	}
	
	public static HashSet<Term> getConstants(Formula formula) {
		HashSet<Term> set = new HashSet<Term>();
		if(formula instanceof Atom) {
			if(formula instanceof DistinctAtom) {
				Term[] newTerms = ((DistinctAtom)formula).getTerms();
				return getConstants(newTerms);
			}
			else if(formula instanceof EqualsAtom) {
				Term[] newTerms = ((EqualsAtom)formula).getTerms();
				return getConstants(newTerms);
			}
			else if(formula instanceof PredicateAtom) {
				Term[] newTerms = ((PredicateAtom)formula).getParameters();
				return getConstants(newTerms);
			}
			else if(formula instanceof VariableAtom) {
//				((VariableAtom) formula).g
				return set; //TODO: irrelevant, oder???
			}
			else {
				return set;  //must be Atom.TRUE/FALSE then..
			}
		}
		else if(formula instanceof ConnectedFormula) {
			Formula lhs = ((ConnectedFormula)formula).getLhs();
			Formula rhs = ((ConnectedFormula)formula).getRhs();
			
			set.addAll(getConstants(lhs));
			set.addAll(getConstants(rhs));
			
			return set;			
		}
		else if(formula instanceof FletFormula) {
			//TODO: sollte eigentlich nicht auftauchen - Lösung richtig??
			set.addAll(getConstants(((FletFormula) formula).getSubFormula()));
			return set;  
//			m_theory.flet(
//					((FletFormula)formula).getVariable(),//um FormulaVariables muss ich mich wohl nicht kümmern.. wohl ..
//					transformFormula(((FletFormula)formula).getValue()), 
//					transformFormula(((FletFormula)formula).getSubFormula()));
		}
		else if(formula instanceof ITEFormula) {
			Formula cond = ((ITEFormula)formula).getCondition();
			Formula trueCase = ((ITEFormula)formula).getTrueCase();
			Formula falseCase = ((ITEFormula)formula).getFalseCase();
			set.addAll(getConstants(cond));
			set.addAll(getConstants(trueCase));
			set.addAll(getConstants(falseCase));

			return set; 
		}
		else if(formula instanceof LetFormula) {
//			Term varTerm = m_VariableNameToTerm.get(
//					m_ConstantsToVariableName.get(
//					((LetFormula)formula).getVariable().getName()));
//			TermVariable var = ((VariableTerm)varTerm).getVariable();
//			
//			Term[] valArray = new Term[1];
//			Term val = ((LetFormula)formula).getValue();
//			valArray[0] = val;
//			val = transformTerms(valArray)[0];
//			
//			Formula form = transformFormula(((LetFormula)formula).getSubFormula());
			HashSet<Term> toAdd = getConstants(((LetFormula)formula).getSubFormula());
			toAdd.remove(((LetFormula)formula).getVariable());
			toAdd.addAll(getConstants(((LetFormula)formula).getValue()));
			set.addAll(toAdd);
			return set;
		}
		else if(formula instanceof NegatedFormula) {
			return getConstants(((NegatedFormula)formula).getSubFormula());
		}
		else if(formula instanceof QuantifiedFormula) {
			HashSet<Term> toAdd = getConstants(((QuantifiedFormula)formula).getSubformula());
			for(TermVariable tv : ((QuantifiedFormula)formula).getVariables())
				toAdd.remove(tv);
			set.addAll(toAdd);
			return set;
		}
		return null;
	}
	
	private static HashSet<Term> getConstants(Term[] terms) {
		HashSet<Term> set = new HashSet<Term>();
		for(Term t : terms) {
			set.addAll(getConstants(t));
		}
		return set;
	}
	
	
	/*
	 * helper for transformAssertions - doing the same thing for terms
	 */
	private static HashSet<Term> getConstants(Term term) {
		HashSet<Term> set = new HashSet<Term>();
		
		if(term instanceof ApplicationTerm) {
			ApplicationTerm term1 = (ApplicationTerm) term;
			if(term1.getParameters().length == 0) 				
				set.add(term1);
			
			return set;
		}
		else if(term instanceof ITETerm) {
			ITETerm term1 = (ITETerm) term;
			Formula cond = term1.getCondition();
			Term trueCase = term1.getTrueCase();
			Term falseCase = term1.getFalseCase();
			set.addAll(getConstants(cond));
			set.addAll(getConstants(trueCase));
			set.addAll(getConstants(falseCase));

			return set;
		}
		else if(term instanceof NumeralTerm) {
//			NumeralTerm terms = (NumeralTerm) term;
			return set;
		}
		else if(term instanceof ProgramVariableTerm) {
//			ProgramVariableTerm term1 = (ProgramVariableTerm) term;
			//TODO: etwas spekulativ - was sind PVTs genau?
			return set;
		}
		else if(term instanceof RationalTerm) {
//			RationalTerm terms1 = (RationalTerm) term;
			return set;//wie's aussieht stecken da keine Variablen drin
		}
		else if(term instanceof VariableTerm) {
			//entscheidender Punkt.. - Ende der Rekursion - positives..
//			VariableTerm term1 = (VariableTerm) term;
//			set.add(term1.getVariable());
			return  set;
		}
		return null;
	}
	
}
