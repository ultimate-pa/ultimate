package local.stalin.boogie.cfgreducer;

import java.util.HashMap;
import java.util.HashSet;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.AbstractAnnotations;
import local.stalin.boogie.cfgreducer.SSAVisitor;

public class SMTEdgeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	private HashMap<TermVariable, TermVariable> m_SSAMapping = new HashMap<TermVariable, TermVariable>();
	HashMap<String, TermVariable>	m_InVars	= new HashMap<String, TermVariable>();
	HashMap<String, TermVariable>	m_OutVars	= new HashMap<String, TermVariable>();
	HashSet<TermVariable> 			m_Vars		= new HashSet<TermVariable>();
	Formula 						m_Assumption= null;
	Theory							m_Theory	= null;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"invars", "outvars", "vars", "assumption"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "invars")
			return m_InVars;
		else if (field == "outvars")
			return m_OutVars;
		else if (field == "vars")
			return m_Vars;
		else if (field == "assumption")
			return m_Assumption;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	public void setInVars(HashMap<String, TermVariable> inVars) {
		m_InVars = inVars;
	}
	public HashMap<String, TermVariable> getInVars(){
		return m_InVars;
	}
	
	public void setOutVars(HashMap<String, TermVariable> outVars) {
		m_OutVars = outVars;
	}
	public HashMap<String, TermVariable> getOutVars(){
		return m_OutVars;
	}
	
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public HashSet<TermVariable> getVars(){
		return m_Vars;
	}
	
	public void setAssumption(Formula assumption) {
		m_Assumption = assumption;
	}
	public Formula getAssumption(){
		return m_Assumption;
	}
	
	public void setTheory(Theory theory){
		m_Theory = theory;
	}
	public Theory getTheory(){
		return m_Theory;
	}
	
	public SMTEdgeAnnotations clone(){
		SMTEdgeAnnotations clone = new SMTEdgeAnnotations();
		
		clone.m_Assumption	= m_Theory.and(Atom.TRUE, m_Assumption);
		clone.m_Theory		= m_Theory;
		clone.m_InVars.putAll(m_InVars);
		clone.m_OutVars.putAll(m_OutVars);
		clone.m_Vars.addAll(m_Vars);
		
		return clone;
	}
	
	public SMTEdgeAnnotations cloneSSA(){
		SMTEdgeAnnotations clone = new SMTEdgeAnnotations();
		clone = this.clone();
		useSSA(clone);
		return clone;
	}
	
	public void useSSA(){
		useSSA(this);
	}
	
	public void setSSAMapping(HashMap<TermVariable, TermVariable> ssaMapping){
		m_SSAMapping = ssaMapping;
	}
	
	private void useSSA(SMTEdgeAnnotations annotations){
		HashMap<TermVariable, TermVariable> variableMapping = m_SSAMapping;
		
		HashMap<String, TermVariable>	inVars		= annotations.getInVars();
		HashMap<String, TermVariable>	outVars		= annotations.getOutVars();
		HashSet<TermVariable>			vars		= annotations.getVars();
		Formula							assumption	= annotations.getAssumption();
		Theory							theory		= annotations.getTheory();
		
		
		HashMap<String, TermVariable>	newInVars	= new HashMap<String, TermVariable>();
		HashMap<String, TermVariable>	newOutVars	= new HashMap<String, TermVariable>();
		HashSet<TermVariable>			newVars		= new HashSet<TermVariable>();
		
		for(String inVarName: inVars.keySet()){
			TermVariable inVar = inVars.get(inVarName);
			TermVariable newInVar = null;
			
			if (variableMapping.containsKey(inVar)){
				newInVar = variableMapping.get(inVar);
			} else {
				newInVar = theory.createFreshTermVariable(inVar.getName(), inVar.getSort());
				variableMapping.put(inVar, newInVar);
			}
			newInVars.put(inVarName, newInVar);
		}
		annotations.setInVars(newInVars);
		
		for(String outVarName: outVars.keySet()){
			TermVariable outVar = outVars.get(outVarName);
			TermVariable newOutVar = null;
			
			if (variableMapping.containsKey(outVar)){
				newOutVar = variableMapping.get(outVar);
			} else {
				newOutVar = theory.createFreshTermVariable(outVar.getName(), outVar.getSort());
				variableMapping.put(outVar, newOutVar);
			}
			newOutVars.put(outVarName, newOutVar);
		}
		annotations.setOutVars(newOutVars);
		
		for(TermVariable var: vars){
			TermVariable newVar = null;
			if (variableMapping.containsKey(var)){
				newVar = variableMapping.get(var);
			} else {
				newVar = theory.createFreshTermVariable(var.getName(), var.getSort());
				variableMapping.put(var, newVar);
			}
			newVars.add(newVar);
		}
		annotations.setVars(newVars);
		
		SSAVisitor		ssaVisitor	= new SSAVisitor(theory, variableMapping);
		FormulaWalker	ssaWalker	= new FormulaWalker(ssaVisitor, theory);
		annotations.setAssumption(ssaWalker.process(assumption));
		return;
	}
}
