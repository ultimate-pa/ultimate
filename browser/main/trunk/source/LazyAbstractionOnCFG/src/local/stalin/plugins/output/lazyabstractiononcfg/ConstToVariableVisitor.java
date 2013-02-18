package local.stalin.plugins.output.lazyabstractiononcfg;

import java.util.HashMap;
import java.util.HashSet;

import local.stalin.boogie.cfgreducer.CFGExplicitNode;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.FormulaWalker.SymbolVisitor;
import local.stalin.model.INode;

public class ConstToVariableVisitor implements SymbolVisitor{

	HashMap<Term, TermVariable>	m_const_to_VariableOfNode	= new HashMap<Term, TermVariable>();
	Theory						m_theory					= null;
	CFGExplicitNode				m_node						= null;
	HashMap<Term, String> 		m_constantsToVariableName	= null;
	
	private HashMap<String, TermVariable>	incomingVariables	= null;
	private HashSet<TermVariable> 			variables			= null;
	
	public ConstToVariableVisitor(HashMap<Term, TermVariable> const_to_VariableOfNode, 
			 HashMap<Term, String> constantsToVariableName, INode node, Theory theory){
		
		m_const_to_VariableOfNode	= const_to_VariableOfNode;
		m_theory					= theory;
		m_node						= (CFGExplicitNode)node;
		m_constantsToVariableName	= constantsToVariableName;
	}
	
	@Override
	public void endscope(TermVariable tv) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void endscopes(TermVariable[] tvs) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void let(TermVariable tv, Term mval) {
		// TODO Auto-generated method stub	
	}

	@Override
	public Formula predicate(PredicateAtom pa) {
		PredicateAtom new_pa = null;
		Term[] n_params = new Term[pa.getParameters().length];
		int i = 0;
		for (Term t: pa.getParameters()){
			n_params[i++] = term(t);
		}
		new_pa = (PredicateAtom)m_theory.atom(pa.getPredicate(), n_params);
		return new_pa;
	}

	@Override
	public void quantifier(TermVariable[] tvs) {
		// TODO Auto-generated method stub
	}

	@SuppressWarnings("unchecked")
	@Override
	public Term term(Term input) {
		Term result = null;
		if (m_const_to_VariableOfNode.containsKey(input)){
			result =  m_theory.term(m_const_to_VariableOfNode.get(input));
		} else if (m_constantsToVariableName.containsKey(input)){
			incomingVariables	= (HashMap<String, TermVariable>)m_node.getSMTAnnotations().getAnnotationsAsMap().get("invars");
			variables 			= (HashSet<TermVariable>)m_node.getSMTAnnotations().getAnnotationsAsMap().get("vars");
			String tempName = m_constantsToVariableName.get(input);
			int ssaPosition = tempName.lastIndexOf("_");
			String name =  tempName.substring(2, ssaPosition);
			TermVariable newVariable = m_theory.createFreshTermVariable("v_" + name, input.getSort());
			incomingVariables.put(name, newVariable);
			variables.add(newVariable);
			result =  m_theory.term(newVariable);
		} else if (input instanceof ApplicationTerm){
			ApplicationTerm aterm = (ApplicationTerm)input;
			Term[] n_params = new Term[aterm.getParameters().length];
			int i = 0;
			for (Term t: (aterm.getParameters())){
				n_params[i++] = term(t);
			}
			ApplicationTerm n_aterm = m_theory.term(aterm.getFunction(), n_params);
			result = n_aterm;
		} else {
			result = input;
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

	@Override
	public void done(Term input) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void done(PredicateAtom pa) {
		// TODO Auto-generated method stub
		
	}

}
