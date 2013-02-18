package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

public class Const2VariableTermTransformer extends TermTransformer{

	HashMap<Term, TermVariable>	m_const_to_VariableOfNode	= new HashMap<Term, TermVariable>();
	Script						m_Script					= null;
	CFGExplicitNode				m_node						= null;
	HashMap<Term, BoogieVar>	m_constantsToBoogieVar		= null;
	
	private HashMap<BoogieVar, TermVariable>	m_incomingVariables	= null;
	private HashSet<TermVariable> 			m_variables			= null;
	
	public Const2VariableTermTransformer(HashMap<Term, TermVariable> const_to_VariableOfNode, 
			 HashMap<Term, BoogieVar> constantsToBoogieVar, INode node, Script script){
		
		m_const_to_VariableOfNode	= const_to_VariableOfNode;
		m_Script					= script;
		m_node						= (CFGExplicitNode)node;
		m_constantsToBoogieVar		= constantsToBoogieVar;
	}
	
	@SuppressWarnings("unchecked")
	protected void convert(Term term) {
		if (m_const_to_VariableOfNode.containsKey(term)){
			super.setResult(m_const_to_VariableOfNode.get(term));
			return;
		} else if (m_constantsToBoogieVar.containsKey(term)){
			m_incomingVariables	= (HashMap<BoogieVar, TermVariable>)m_node.getSMTAnnotations().getAnnotationsAsMap().get("invars");
			m_variables 			= (HashSet<TermVariable>)m_node.getSMTAnnotations().getAnnotationsAsMap().get("vars");
			BoogieVar boogieVar = m_constantsToBoogieVar.get(term);
			TermVariable newVariable = VariableSSAManager.getFreshTermVariable(boogieVar, term.getSort());
			m_incomingVariables.put(boogieVar, newVariable);
			m_variables.add(newVariable);
			super.setResult(newVariable);
			return;
		}
		super.convert(term);
	}
}
