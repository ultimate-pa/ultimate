package local.stalin.boogie.cfgreducer;

import java.util.HashMap;
import java.util.HashSet;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.AbstractAnnotations;

public class SMTNodeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	static HashMap<String, TermVariable> s_OldVars = new HashMap<String, TermVariable>();
	
	HashMap<String, TermVariable> 		m_InVars			= new HashMap<String, TermVariable>();
	HashMap<TermVariable, TermVariable> m_VariableMapping	= new HashMap<TermVariable, TermVariable>();
	public boolean						m_clonedUsingSSA	= false;
	HashSet<TermVariable>				m_Vars				= new HashSet<TermVariable>();
	Formula								m_Assertion			= null;
	Theory								m_Theory			= null;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = { 
		"invars", "vars", "oldvars", "assertion"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "invars")
			return m_InVars;
		else if (field == "oldvars")
			return s_OldVars;
		else if (field == "vars")
			return m_Vars;
		else if (field == "assertion")
			return m_Assertion;
		else 
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	public void setInVars(HashMap<String, TermVariable> inVars) {
		m_InVars = inVars;
	}
	public HashMap<String, TermVariable> getInVars(){
		return m_InVars;
	}
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public HashSet<TermVariable> getVars(){
		return m_Vars;
	}
	public void setOldVars(HashMap<String, TermVariable> oldVars) {
		s_OldVars = oldVars;
	}
	public HashMap<String, TermVariable> getOldVars(){
		return s_OldVars;
	}
	public void setAssertion(Formula assertion) {
		m_Assertion = assertion;
	}
	public Formula getAssertion(){
		return m_Assertion;
	}
	public void setTheory(Theory theory){
		m_Theory = theory;
	}
	public Theory getTheory(){
		return m_Theory;
	}
	public SMTNodeAnnotations clone(){
		SMTNodeAnnotations clone = new SMTNodeAnnotations();
		
		clone.m_Assertion	= m_Theory.and(Atom.TRUE, m_Assertion);
		clone.m_Theory		= m_Theory;
		clone.m_InVars.putAll(m_InVars);
		clone.m_Vars.addAll(m_Vars);
		
		m_clonedUsingSSA = false;
		return clone;
	}
	
	public SMTNodeAnnotations cloneSSA(){
		SMTNodeAnnotations clone = new SMTNodeAnnotations();
		clone = this.clone();
		useSSA(clone);
		return clone;
	}
	
	public void useSSA(){
		useSSA(this);
	}
	private void useSSA(SMTNodeAnnotations annotations){
		m_clonedUsingSSA = true;
		
		HashMap<String, TermVariable>	inVars		= annotations.getInVars();
		HashSet<TermVariable>			vars		= annotations.getVars();
		Formula							assertion	= annotations.getAssertion();
		Theory							theory		= annotations.getTheory();
		
		m_VariableMapping.clear();
		
		HashMap<String, TermVariable> newInVars		= new HashMap<String, TermVariable>();
		HashSet<TermVariable> newVars				= new HashSet<TermVariable>();
		
		for(String inVarName: inVars.keySet()){
			TermVariable inVar = inVars.get(inVarName);
			TermVariable newInVar = theory.createFreshTermVariable(inVar.getName(), inVar.getSort());
			m_VariableMapping.put(inVar, newInVar);
			newInVars.put(inVarName, newInVar);
		}
		annotations.setInVars(newInVars);
		
		for(TermVariable var: vars){
			TermVariable newVar = null;
			if (m_VariableMapping.containsKey(var)){
				newVar = m_VariableMapping.get(var);
			} else {
				newVar = theory.createFreshTermVariable(var.getName(), var.getSort());
				m_VariableMapping.put(var, newVar);
			}
			newVars.add(newVar);
		}
		annotations.setVars(newVars);;
		
		SSAVisitor		ssaVisitor	= new SSAVisitor(theory, m_VariableMapping);
		FormulaWalker	ssaWalker	= new FormulaWalker(ssaVisitor, theory);
		annotations.setAssertion(ssaWalker.process(assertion));
	}
	
	public HashMap<TermVariable, TermVariable> getSSAMapping(){
		return m_VariableMapping;
	}
}
