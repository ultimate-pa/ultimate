package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SSATermTransformer;

public class SMTNodeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	static HashMap<String, TermVariable> s_OldVars = new HashMap<String, TermVariable>();
	
	HashMap<BoogieVar, TermVariable> 		m_InVars			= new HashMap<BoogieVar, TermVariable>();
	HashMap<TermVariable, TermVariable> m_VariableMapping	= new HashMap<TermVariable, TermVariable>();
	public boolean						m_clonedUsingSSA	= false;
	HashSet<TermVariable>				m_Vars				= new HashSet<TermVariable>();
	Term								m_Assertion			= null;
	Script								m_Script			= null;
	static int							s_newVarCounter		= 0;

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

	public void setInVars(HashMap<BoogieVar, TermVariable> inVars) {
		m_InVars = inVars;
	}
	public HashMap<BoogieVar, TermVariable> getInVars(){
		return m_InVars;
	}
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public HashSet<TermVariable> getVars(){
		return m_Vars;
	}
//	public void setOldVars(HashMap<String, TermVariable> oldVars) {
//		s_OldVars = oldVars;
//	}
//	public HashMap<String, TermVariable> getOldVars(){
//		return s_OldVars;
//	}
	public void setAssertion(Term assertion) {
		m_Assertion = assertion;
	}
	public Term getAssertion(){
		return m_Assertion;
	}
	public void setScript(Script script){
		m_Script = script;
	}
	public Script getScript(){
		return m_Script;
	}
	public SMTNodeAnnotations clone(){
		SMTNodeAnnotations clone = new SMTNodeAnnotations();
		
		clone.m_Assertion	= Util.and(m_Script, (m_Script.term("true")), m_Assertion);
		clone.m_Script		= m_Script;
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
		annotations.m_clonedUsingSSA = true;
		
		HashMap<BoogieVar, TermVariable>	inVars	= annotations.getInVars();
		HashSet<TermVariable>			vars		= annotations.getVars();
		Term							assertion	= annotations.getAssertion();
		
		annotations.m_VariableMapping.clear();
		
		HashMap<BoogieVar, TermVariable> newInVars	= new HashMap<BoogieVar, TermVariable>();
		HashSet<TermVariable> newVars				= new HashSet<TermVariable>();
		
		for(BoogieVar boogieInVar: inVars.keySet()){
			TermVariable inVar = inVars.get(boogieInVar);
			TermVariable newInVar = VariableSSAManager.getFreshTermVariable(boogieInVar, inVar.getSort());
			annotations.m_VariableMapping.put(inVar, newInVar);
			newInVars.put(boogieInVar, newInVar);
		}
		annotations.setInVars(newInVars);
		
		for(TermVariable var: vars){
			TermVariable newVar = null;
			if (annotations.m_VariableMapping.containsKey(var)){
				newVar = annotations.m_VariableMapping.get(var);
			} else {
				newVar = VariableSSAManager.getFreshTermVariable(var);
				// TODO do we need new name for this newVar?
				annotations.m_VariableMapping.put(var, newVar);
			}
			newVars.add(newVar);
		}
		annotations.setVars(newVars);
		
		SSATermTransformer ssaTermTransformer = new SSATermTransformer(m_Script, annotations.m_VariableMapping);
		annotations.setAssertion(ssaTermTransformer.transform(assertion));
		
//		SSAVisitor		ssaVisitor	= new SSAVisitor(script, m_VariableMapping);
//		FormulaWalker	ssaWalker	= new FormulaWalker(ssaVisitor, script);
//		annotations.setAssertion(ssaWalker.process(assertion));
	}
	
	public HashMap<TermVariable, TermVariable> getSSAMapping(){
		return m_VariableMapping;
	}
}
