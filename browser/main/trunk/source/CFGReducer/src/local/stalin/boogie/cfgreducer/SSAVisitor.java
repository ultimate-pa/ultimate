package local.stalin.boogie.cfgreducer;

import java.util.HashMap;
import java.util.HashSet;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;

public class SSAVisitor implements SymbolVisitor {

	private HashMap<TermVariable, TermVariable> m_VariableMapping 	= null;
	private Theory								m_Theory			= null;
	private HashSet<TermVariable>				m_ActiveVariables	= null;

	public SSAVisitor(Theory theory, HashMap<TermVariable, TermVariable> variableMapping){
		m_Theory 			= theory;
		m_VariableMapping	= variableMapping;
		m_ActiveVariables= new HashSet<TermVariable>();
	}
	
	@Override
	public void done(Term input) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void done(PredicateAtom pa) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void endscope(TermVariable tv) {
		m_ActiveVariables.remove(tv);
	}

	@Override
	public void endscopes(TermVariable[] tvs) {
		for(TermVariable tv: tvs){
			m_ActiveVariables.remove(tv);
		}
	}

	@Override
	public void let(TermVariable tv, Term mval) {
		m_ActiveVariables.add(tv);
	}

	@Override
	public Formula predicate(PredicateAtom pa) {
		return null;
	}

	@Override
	public void quantifier(TermVariable[] tvs) {
		for(TermVariable tv: tvs){
			m_ActiveVariables.add(tv);
		}
	}

	@Override
	public Term term(Term input) {
		Term result = input;
		if (input instanceof VariableTerm){
			TermVariable tv		= ((VariableTerm) input).getVariable();
			if (m_VariableMapping.containsKey(tv) && !m_ActiveVariables.contains(tv)){
				result = m_Theory.term(m_VariableMapping.get(tv));
			}
		} else if (input instanceof ApplicationTerm){
			result = null;
		} else if (input instanceof ITETerm){
			result = null;
		} 
		return result;
	}

	@Override
	public boolean unflet() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean unlet() {
		// TODO Auto-generated method stub
		return false;
	}

}
