package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.util.Util;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SSATermTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

public class SMTEdgeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	private HashMap<TermVariable, TermVariable> m_SSAMapping = new HashMap<TermVariable, TermVariable>();
	HashMap<BoogieVar, TermVariable>	m_InVars	= new HashMap<BoogieVar, TermVariable>();
	HashMap<BoogieVar, TermVariable>	m_OutVars	= new HashMap<BoogieVar, TermVariable>();
	HashSet<TermVariable> 			m_Vars		= new HashSet<TermVariable>();
	Term							m_PositiveEdgeIdFormula = null;
	HashSet<TermVariable>			m_EdgeIds = null;
	Term	 						m_Assumption= null;
	Script							m_Script	= null;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"invars", "outvars", "vars", "assumption", "edgeidformula", "edgeids"
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
		else if (field == "edgeidformula")
			return m_PositiveEdgeIdFormula;
		else if (field == "edgeids")
			return m_EdgeIds;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	public BoogieVar initEdgeId(String newEdgeId) {
		BoogieVar boogieVar = new BoogieVar(newEdgeId, null, BoogieType.boolType, false);
		TermVariable tvId = VariableSSAManager.getFreshTermVariable(boogieVar, m_Script.sort("Bool"));
		m_Vars.add(tvId);
		m_OutVars.put(boogieVar, tvId);
		m_PositiveEdgeIdFormula = m_Script.term("=", tvId, m_Script.term("true"));
		m_EdgeIds = new HashSet<TermVariable>();
		m_EdgeIds.add(tvId);
		return boogieVar;
	}
	
	public void addOrEdgeId(Term newPositiveEdgeIdFormula, HashSet<TermVariable> newIds) {
		Term negativeEdgeIdFormula = m_Script.term("true");
		Term newNegativeEdgeIdFormula = m_Script.term("true");
		HashSet<TermVariable> intersectingIds = new HashSet<TermVariable>();
		intersectingIds.addAll(newIds);
		intersectingIds.retainAll(m_EdgeIds);
		HashSet<TermVariable> disjunctIdsOfThisEdge = new HashSet<TermVariable>();
		HashSet<TermVariable> disjunctIdsOfOtherEdge = new HashSet<TermVariable>();
		disjunctIdsOfThisEdge.addAll(m_EdgeIds);
		disjunctIdsOfThisEdge.removeAll(intersectingIds);
		disjunctIdsOfOtherEdge.addAll(newIds);
		disjunctIdsOfOtherEdge.removeAll(intersectingIds);
		for (TermVariable tv: disjunctIdsOfThisEdge) {
			negativeEdgeIdFormula = Util.and(m_Script, negativeEdgeIdFormula,
					m_Script.term("=", tv, m_Script.term("false")));
		}
		for (TermVariable tv: disjunctIdsOfOtherEdge) {
			newNegativeEdgeIdFormula = Util.and(m_Script, newNegativeEdgeIdFormula,
					m_Script.term("=", tv, m_Script.term("false")));
		}
		m_PositiveEdgeIdFormula = Util.or(m_Script,  Util.and(m_Script, m_PositiveEdgeIdFormula, newNegativeEdgeIdFormula),
				Util.and(m_Script, newPositiveEdgeIdFormula, negativeEdgeIdFormula));
		m_EdgeIds.addAll(newIds);
	}

	public void addAndEdgeId(Term newPositiveEdgeIdFormula, HashSet<TermVariable> ids) {
		m_PositiveEdgeIdFormula = Util.and(m_Script,  m_PositiveEdgeIdFormula, newPositiveEdgeIdFormula);
		m_EdgeIds.addAll(ids);
	}
	
	public void setEdgeIdFormula(Term positiveEdgeIdFormula, HashSet<TermVariable> ids) {
		m_PositiveEdgeIdFormula = positiveEdgeIdFormula;
		m_EdgeIds = new HashSet<TermVariable>();
		m_EdgeIds.addAll(ids);
	}
	
	public Term getPositiveEdgeIdFormula() {
		return m_PositiveEdgeIdFormula;
	}
	
	public Term getNegativeEdgeIdFormula(HashSet<TermVariable> ids) {
		Term negativeEdgeIdFormula = m_Script.term("true");
		HashSet<TermVariable> intersectingIds = new HashSet<TermVariable>();
		intersectingIds.addAll(ids);
		intersectingIds.retainAll(m_EdgeIds);
		HashSet<TermVariable> disjunctIds = new HashSet<TermVariable>();
		disjunctIds.addAll(m_EdgeIds);
		disjunctIds.removeAll(intersectingIds);
		for (TermVariable tv: disjunctIds) {
			negativeEdgeIdFormula = Util.and(m_Script, negativeEdgeIdFormula,
					m_Script.term("=", tv, m_Script.term("false")));
		}
		return negativeEdgeIdFormula;
}
	
	public HashSet<TermVariable> getEdgeIds() {
		return m_EdgeIds;
	}
	
	public void setInVars(HashMap<BoogieVar, TermVariable> inVars) {
		m_InVars = inVars;
	}
	public HashMap<BoogieVar, TermVariable> getInVars(){
		return m_InVars;
	}
	
	public void setOutVars(HashMap<BoogieVar, TermVariable> outVars) {
		m_OutVars = outVars;
	}
	public HashMap<BoogieVar, TermVariable> getOutVars(){
		return m_OutVars;
	}
	
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public HashSet<TermVariable> getVars(){
		return m_Vars;
	}
	
	public void setAssumption(Term assumption) {
		m_Assumption = assumption;
	}
	public Term getAssumption(){
		return m_Assumption;
	}
	
	public void setScript(Script theory){
		m_Script = theory;
	}
	public Script getScript(){
		return m_Script;
	}
	
	public SMTEdgeAnnotations clone(){
		SMTEdgeAnnotations clone = new SMTEdgeAnnotations();
		
		clone.m_Assumption	= Util.and(m_Script, m_Script.term("true"), m_Assumption);
		clone.m_Script		= m_Script;
		clone.m_InVars.putAll(m_InVars);
		clone.m_OutVars.putAll(m_OutVars);
		clone.m_Vars.addAll(m_Vars);
		if (m_PositiveEdgeIdFormula != null)  {
			clone.m_PositiveEdgeIdFormula = Util.and(m_Script, m_Script.term("true"), m_PositiveEdgeIdFormula);
			clone.m_EdgeIds = new HashSet<TermVariable>();
			clone.m_EdgeIds.addAll(m_EdgeIds);
		} else {
			clone.m_PositiveEdgeIdFormula = null;
			clone.m_EdgeIds = null;
		}
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
		
		HashMap<BoogieVar, TermVariable>	inVars		= annotations.getInVars();
		HashMap<BoogieVar, TermVariable>	outVars		= annotations.getOutVars();
		HashSet<TermVariable>			vars		= annotations.getVars();
		HashSet<TermVariable>			edgeIds		= annotations.getEdgeIds();
		Term							assumption	= annotations.getAssumption();
		Term							edgeIdFormula = annotations.getPositiveEdgeIdFormula();
		Script							script		= annotations.getScript();
		
		
		HashMap<BoogieVar, TermVariable>	newInVars	= new HashMap<BoogieVar, TermVariable>();
		HashMap<BoogieVar, TermVariable>	newOutVars	= new HashMap<BoogieVar, TermVariable>();
		HashSet<TermVariable>			newVars		= new HashSet<TermVariable>();
		HashSet<TermVariable>			newEdgeIds	= new HashSet<TermVariable>();
		
		for(BoogieVar boogieInVar: inVars.keySet()){
			TermVariable inVar = inVars.get(boogieInVar);
			TermVariable newInVar = null;
			
			if (variableMapping.containsKey(inVar)){
				newInVar = variableMapping.get(inVar);
			} else {
				newInVar = VariableSSAManager.getFreshTermVariable(boogieInVar, inVar.getSort());
				variableMapping.put(inVar, newInVar);
			}
			newInVars.put(boogieInVar, newInVar);
		}
		annotations.setInVars(newInVars);
		
		for(BoogieVar boogieOutVar: outVars.keySet()){
			TermVariable outVar = outVars.get(boogieOutVar);
			TermVariable newOutVar = null;
			
			if (variableMapping.containsKey(outVar)){
				newOutVar = variableMapping.get(outVar);
			} else {
				newOutVar = VariableSSAManager.getFreshTermVariable(boogieOutVar, outVar.getSort());
				variableMapping.put(outVar, newOutVar);
			}
			newOutVars.put(boogieOutVar, newOutVar);
		}
		annotations.setOutVars(newOutVars);
		
		for(TermVariable var: vars){
			TermVariable newVar = null;
			if (variableMapping.containsKey(var)){
				newVar = variableMapping.get(var);
			} else {
				newVar = script.variable(var.getName(), var.getSort());
				// TODO do we need new name for this newVar?
				variableMapping.put(var, newVar);
			}
			newVars.add(newVar);
		}
		annotations.setVars(newVars);
		
		SSATermTransformer ssaTermTransformer = new SSATermTransformer(script, variableMapping);
		annotations.setAssumption(ssaTermTransformer.transform(assumption));
		
		if (edgeIdFormula != null) {
			assert(!edgeIds.isEmpty());
			for(TermVariable var: edgeIds){
				TermVariable newVar = null;
				if (variableMapping.containsKey(var)){
					newVar = variableMapping.get(var);
				} else {
					newVar = script.variable(var.getName(), var.getSort());
					// TODO do we need new name for this newVar?
					variableMapping.put(var, newVar);
				}
				newEdgeIds.add(newVar);
			}
			annotations.setEdgeIdFormula(ssaTermTransformer.transform(edgeIdFormula), newEdgeIds);
		}
		return;
	}
	
	public boolean hasIds() {
		return m_PositiveEdgeIdFormula != null;
	}
}
