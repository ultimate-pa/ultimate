package local.stalin.plugins.output.lazyabstractiononcfg;

import java.util.ArrayList;
import java.util.HashMap;
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
import local.stalin.logic.Theory;
import local.stalin.logic.VariableAtom;
import local.stalin.logic.VariableTerm;

/*
 * takes a formula an replaces all variables which correspond to the same program variable
 * with _one_ of its ssa-versions
 */
public class VariableEqualizer {

	// -------------------------------------------------------------------------
	//------------------------ formula walking stuff ---------------------------
	// ------------------------------------------------------------------------
	
	static Theory m_theory;
	static HashMap<TermVariable, String> m_tvToName;
	static HashMap<String, TermVariable> m_stringToTv;
	
	private static Formula equalizeVariables(Formula assertion) {
		return equalizeVariables(assertion, m_tvToName,  m_stringToTv,
				 m_theory);
	}
	
	/*
	 * transform an assertion coming from a set of interpolants 
	 * (the assertions in the nodes in lazy abstraction)
	 * in such a way that all its Termvariables are replaced by their nonSSA-counterparts
	 */
	public static Formula equalizeVariables(Formula assertion, 
			HashMap<TermVariable, String> tvToName, HashMap<String, TermVariable> stringToTv,
			Theory theory) {
		m_theory = theory;
		m_tvToName = tvToName;
		m_stringToTv = stringToTv;
		
		if(assertion instanceof Atom) {
			if(assertion instanceof DistinctAtom) {
				Term[] newTerms = equalizeVariables(((DistinctAtom)assertion).getTerms());
				return m_theory.equals(newTerms);
			}
			else if(assertion instanceof EqualsAtom) {
				Term[] newTerms = equalizeVariables(((EqualsAtom)assertion).getTerms());
				return m_theory.equals(newTerms);
			}
			else if(assertion instanceof PredicateAtom) {
				Term[] newTerms = equalizeVariables(((PredicateAtom)assertion).getParameters());
				return m_theory.atom(((PredicateAtom)assertion).getPredicate(), newTerms);
			}
			else if(assertion instanceof VariableAtom) {
				return assertion;
			}
			else {
				return assertion; //must be Atom.TRUE/FALSE then..
			}
		}
		else if(assertion instanceof ConnectedFormula) {
			Formula lhs = equalizeVariables(((ConnectedFormula)assertion).getLhs());
			Formula rhs = equalizeVariables(((ConnectedFormula)assertion).getRhs());
			
			switch(((ConnectedFormula)assertion).getConnector()) {
			case 0:
				return m_theory.or(lhs, rhs);
			case 1:
				return m_theory.and(lhs, rhs);
			case 2:
				return m_theory.implies(lhs, rhs);
			case 3:
				return m_theory.iff(lhs, rhs);
			case 4:
				return m_theory.xor(lhs, rhs);
			case 5:
				return m_theory.oeq(lhs, rhs);					
			}
			
		}
		else if(assertion instanceof FletFormula) {
			return m_theory.flet(
					((FletFormula)assertion).getVariable(),//um FormulaVariables muss ich mich wohl nicht kümmern.. wohl ..
					equalizeVariables(((FletFormula)assertion).getValue()), 
					equalizeVariables(((FletFormula)assertion).getSubFormula()));
		}
		else if(assertion instanceof ITEFormula) {
			Formula cond = equalizeVariables(((ITEFormula)assertion).getCondition());
			Formula trueCase = equalizeVariables(((ITEFormula)assertion).getTrueCase());
			Formula falseCase = equalizeVariables(((ITEFormula)assertion).getFalseCase());
			return m_theory.ifthenelse(cond, trueCase, falseCase);
		}
		else if(assertion instanceof LetFormula) {
//			Term varTerm = m_VariableNameToTerm.get(
//					m_ConstantsToVariableName.get(
//					((LetFormula)assertion).getVariable().getName()));
//			TermVariable var = ((VariableTerm)varTerm).getVariable();
//			
//			Term[] valArray = new Term[1];
//			Term val = ((LetFormula)assertion).getValue();
//			valArray[0] = val;
//			val = equalizeVariables(valArray)[0];
//			Hack... - again
			String inProgName = new String();
			String name = ((LetFormula)assertion).getVariable().getName();
			
			if(m_tvToName.get(name) == null) {

				String[] spl = name.split("_");

				for(int i = 0; i < spl.length; i++) {
					if(i == 1)
						inProgName = spl[i];
					else if(i < 0 && i != spl.length-1) 
						inProgName.concat("_" + spl[i]);
				}
			}
			else {
				inProgName = m_tvToName.get(name);
			}
			
			TermVariable var = m_stringToTv.get(inProgName);
			Term val = equalizeVariables(((LetFormula)assertion).getValue());
			Formula form = equalizeVariables(((LetFormula)assertion).getSubFormula());
					
			return m_theory.let(var, val, form);
		}
		else if(assertion instanceof NegatedFormula) {
			return m_theory.not(equalizeVariables(((NegatedFormula)assertion).getSubFormula()));
		}
		else if(assertion instanceof QuantifiedFormula) {
			switch(((QuantifiedFormula)assertion).getQuantifier()){
			case 0:
				return m_theory.exists(
						((QuantifiedFormula)assertion).getVariables(), ((QuantifiedFormula)assertion).getSubformula());
			case 1: 
				return m_theory.forall(
						((QuantifiedFormula)assertion).getVariables(), ((QuantifiedFormula)assertion).getSubformula());
			}
			//Achtung - keine Rekursion hier TODO: vermutlich müssen die quantifizierten Variablen 
			//bei der Transformation ausgespart werden
		}
		return null;
	}

	private static Term[] equalizeVariables(Term[] terms) {
		ArrayList<Term> toReturn = new ArrayList<Term>();
		for(Term t : terms) {
			toReturn.add(equalizeVariables(t));
		}
		return toReturn.toArray(terms);
	}
	
	
	/*
	 * helper for transformAssertions - doing the same thing for terms
	 */
	private static Term equalizeVariables(Term term) {
//		ArrayList<Term> toReturn = new ArrayList<Term>();
		
		if(term instanceof ApplicationTerm) {
//			ApplicationTerm term1 = (ApplicationTerm) term;
//			if(term1.getParameters().length != 0) {
//				return m_theory.term(term1.getFunction(), equalizeVariables(term1.getParameters()));
//			}
//			else {
//				Term tr = m_VariableNameToTerm.get(m_ConstantsToVariableName.get(term1));
//				if(tr == null)
//					throw new NullPointerException();
//				return tr;
//			}
			return term;			
		}
		else if(term instanceof ITETerm) {
			ITETerm term1 = (ITETerm) term;

			Term trueCase = equalizeVariables(term1.getTrueCase());
			Term falseCase = equalizeVariables(term1.getFalseCase());

			return m_theory.ite(equalizeVariables(term1.getCondition()),
					trueCase, falseCase);
		}
		else if(term instanceof NumeralTerm) {
//			NumeralTerm terms = (NumeralTerm) term;
			return term;
		}
		else if(term instanceof ProgramVariableTerm) {
			ProgramVariableTerm term1 = (ProgramVariableTerm) term;
			//TODO: etwas spekulativ - was sind PVTs genau?
			return term;
		}
		else if(term instanceof RationalTerm) {
//			RationalTerm terms1 = (RationalTerm) term;
			return term;//wie's aussieht stecken da keine Variablen drin
		}
		else if(term instanceof VariableTerm) {
			//ev quatsch/dürfte nicht vorkommen, da konstanten als 0-stellige Fkten modelliert sind
			VariableTerm term1 = (VariableTerm) term;
			
			String inProgName = new String();
			String name = term1.getVariable().getName();
			
			if(m_tvToName.get(name) == null) {

				String[] spl = name.split("_");

				for(int i = 0; i < spl.length; i++) {
					if(i == 1)
						inProgName = spl[i];
					else if(i < 0 && i != spl.length-1) 
						inProgName.concat("_" + spl[i]);
				}
			}
			else {
				inProgName = m_tvToName.get(name);
			}

			
			return m_theory.term(m_stringToTv.get(inProgName));
		}
		return null;
	}
	
}
