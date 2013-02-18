package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.PayloadModifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.SMTInterface;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;

public class CFGEdge implements IEdge {

	/**
	 * 
	 */
	private static final long serialVersionUID = 5142112003169579223L;

	private CFGExplicitNode 	m_Source = null;
	private CFGExplicitNode 	m_Target = null;
	
	//added by alex
	public static HashMap<String, Term> s_declaredSMTConstants = new HashMap<String, Term>(); 
	
	static private HashMap<BoogieVar, CFGEdge>	s_allEdgeIds = new HashMap<BoogieVar, CFGEdge>();
	private Payload 			m_Payload 		= new Payload();
	private Script				m_Script;
	private static Logger		s_Logger		= UltimateServices.getInstance().getLogger("CFGEdge");
	private SMTInterface 		m_SMTInterface	= null;
	private static int			s_TheoremProverCalls 	= 0;
	private static long			s_totalTime				= 0;
//	private boolean				m_hasId					= false;
	private HashMap<Term, Term> m_substitutionMap = new HashMap<Term, Term>();
	
//	IEclipsePreferences 		s_prefs	= null;
	
	public CFGEdge(Script script, Term assumption, INode source, INode target){
		m_Script = script;
		m_SMTInterface = new SMTInterface(m_Script);
		setSource((CFGExplicitNode)source);
		setTarget((CFGExplicitNode)target);
		HashMap<String, IAnnotations>	annotations = new HashMap<String, IAnnotations>();
		SMTEdgeAnnotations				annotation	= new SMTEdgeAnnotations();
		annotations.put("SMT", annotation);
		annotation.setScript(script);
		assumption = assumption != null? assumption: m_Script.term("true");
		annotation.setAssumption(assumption);
		m_Payload.setAnnotations(annotations);
	}
	
	public void addSubstitution(Term term, Term substitute) {
		for(Entry<Term, Term> entry: m_substitutionMap.entrySet()) {
			if(entry.getValue().equals(term)) {
				m_substitutionMap.put(entry.getKey(), substitute);
			}
		}
		m_substitutionMap.put(term, substitute);
	}
	
	public void setSubstitution(HashMap<Term,Term> substitutionMap) {
		m_substitutionMap = substitutionMap;
	}
	
	public void addSubstitution(HashMap<Term,Term> substitutionMap) {
		m_substitutionMap.putAll(substitutionMap);
	}
	
	public HashMap<Term,Term> getSubstitutionMap() {
		return m_substitutionMap;
	}
	
	public void applySubstitution() {
		if(m_substitutionMap.isEmpty()) {
			return;
		}
		SubstituteTermTransformer subTermTransformer =
				new SubstituteTermTransformer();
		this.setAssumption(subTermTransformer.substitute(getAssumption(),
				m_substitutionMap));
		m_substitutionMap = new HashMap<Term, Term>();
		
	}
	
	public ILocation getLocation() {
		return this.m_Payload.getLocation();
	}
	
	public void makeId() {
		String tname = getTarget().getPayload().getName().replaceAll("[\\W]", "");;
		String sname = getSource().getPayload().getName().replaceAll("[\\W]", "");;
		String id = sname + "_" + tname;
		makeId(id);
	}
	
	public void makeId(String id) {
		SMTEdgeAnnotations annotation = getSMTAnnotations();
		BoogieVar edgeId = annotation.initEdgeId(id);
		annotation.setAssumption(Util.and(m_Script,
				annotation.getAssumption(), annotation.getPositiveEdgeIdFormula()));
		s_allEdgeIds.put(edgeId, this);
	}
	
	@Override
	public INode getSource() {
		return m_Source;
	}

	@Override
	public INode getTarget() {
		return m_Target;
	}

	public Script getScript() {
		return m_Script;
	}
	
	public void resetStats() {
		s_TheoremProverCalls = 0;
		s_totalTime = 0;
	}
	
	public void clearEdgeStaticData() {
		s_allEdgeIds.clear();
		s_declaredSMTConstants.clear();
//		s_subTermTransformer = new SubstituteTermTransformer();
	}
	
	public int getTheoremProverCount() {
		return s_TheoremProverCalls;
	}
	
	public long getTotalTime() {
		return s_totalTime;
	}
	
	@Override
	public void setSource(INode source) {
		CFGExplicitNode oldSource = m_Source;
		m_Source = (CFGExplicitNode)source;
		
		if(source != null && 
				!source.getOutgoingEdges().contains(this)){
			source.addOutgoingEdge(this);
		}
		if(oldSource != null && 
				oldSource.getOutgoingEdges().contains(this)){
			oldSource.removeOutgoingEdge(this);
		}
		checkName();
	}

	@Override
	public void setTarget(INode target) {
		CFGExplicitNode oldTarget = m_Target;
		m_Target = (CFGExplicitNode)target;
		
		if(target != null && 
				!target.getIncomingEdges().contains(this)){
			target.addIncomingEdge(this);
		}
		if(oldTarget != null && 
				oldTarget.getIncomingEdges().contains(this)){
			oldTarget.removeIncomingEdge(this);
		}
		checkName();
	}

	public void checkName(){
		if(m_Source != null && m_Target != null){
			m_Payload.setName(m_Source.getPayload().getName() + "->" + m_Target.getPayload().getName());
		}
	}
	
	@Override
	public IPayload getPayload() {
		return m_Payload;
	}

	public SMTEdgeAnnotations getSMTAnnotations(){
		return (SMTEdgeAnnotations)m_Payload.getAnnotations().get("SMT");
	}
	
	@Override
	public boolean hasPayload() {
		return m_Payload.isValue();
	}

	public void setPayload(IPayload payload) {
		m_Payload = (Payload)payload;
		setAssumption(getAssumption()); //Sets the assumption to TRUE if it's null
		checkName();
	}

	public Term getAssumption(){
		return getSMTAnnotations() != null? getSMTAnnotations().getAssumption(): m_Script.term("true");
	}
	
	public HashMap<BoogieVar, CFGEdge> getAllEdgeIds(){
		return s_allEdgeIds;
	}
	
	public boolean useIdTags() {
		return (!s_allEdgeIds.isEmpty());
	}
	
	public void setAssumption(Term assumption){
		assumption = assumption != null? assumption: m_Script.term("true");
		getSMTAnnotations().setAssumption(assumption);
	}
	
	public boolean deleteEdge(){
		boolean result = true;
		if (m_Source != null){
			result = m_Source.removeOutgoingEdge(this);
		}
		if (m_Target != null){
			result = result? m_Target.removeIncomingEdge(this): false;
		}
		return (result);
	}
	
	public CFGEdge copyWithoutNodes(){
		return copyWithoutNodes(false);
	}
	
	//Clones edge, its payload and its CFGEdgeAnnotaions
	private CFGEdge copyWithoutNodes(boolean usingSSA){
		CFGEdge newCFGEdge = new CFGEdge(m_Script, null, null, null);
		Payload newPayload = usingSSA? PayloadModifier.copyPayloadWithSSA(m_Payload): PayloadModifier.copyPayload(m_Payload);
		
		newCFGEdge.setPayload(newPayload);
		
		//newCFGEdge.m_SMTInterface = m_SMTInterface;
		
		newCFGEdge.checkName();
		return newCFGEdge;
	}
	
	public CFGEdge copyWithoutNodesUsingSSAMapping(HashMap<TermVariable, TermVariable> ssaMapping){
		getSMTAnnotations().setSSAMapping(ssaMapping);
		CFGEdge newEdge = copyWithoutNodes(true);
		return newEdge;
	}
	
	public LBool checkSatisfiability(){
		return checkEdge(false);
	}
	
	public LBool checkValidity(){
		return checkEdge(true);
	}
	
	public LBool checkEdge(boolean negateTarget){
//		applySubstitution();
		CFGExplicitNode source = m_Source;
		CFGExplicitNode target = m_Target;
		
		if (m_Source == m_Target){
			target = m_Source.copyWithoutEdgesWithSSA();
		}
		
		Term target_assertion	= target.getAssertion();
		Term assumption			= getAssumption();
		Term formula				= null;
		
		SMTEdgeAnnotations annotation = getSMTAnnotations();
		
		HashMap<BoogieVar, TermVariable>target_inVars	= target.getSMTAnnotations().getInVars();
		HashSet<TermVariable> 			target_Vars		= target.getSMTAnnotations().getVars();		
		
		HashSet<TermVariable>			vars				= new HashSet<TermVariable>();
		
		Term							source_assertion	= m_Script.term("true");
		HashMap<BoogieVar, TermVariable>source_inVars		= new HashMap<BoogieVar, TermVariable>();
		HashSet<TermVariable>			source_Vars			= new HashSet<TermVariable>();
		
		if (source.getSMTAnnotations() != null){
			source_assertion	= source.getAssertion();
			source_inVars		= source.getSMTAnnotations().getInVars();
			source_Vars			= source.getSMTAnnotations().getVars();
		}
		HashMap<BoogieVar, TermVariable>	edge_inVars			= annotation.getInVars();
		HashMap<BoogieVar, TermVariable>	edge_outVars		= annotation.getOutVars();
		HashSet<TermVariable>				edge_Vars			= annotation.getVars();
		
//		HashMap<BoogieVar, TermVariable>	oldVars				= SMTNodeAnnotations.s_OldVars;
		
		vars.addAll(source_Vars);
		vars.addAll(target_Vars);
		vars.addAll(edge_Vars);
//		HashMap<Term, Term> subTermMapping = new HashMap<Term, Term>();
//		SubstituteTermTransformer subTermTransformer = new SubstituteTermTransformer();
		
		for (BoogieVar targetInBoogieVar: target_inVars.keySet()){
			if (edge_outVars.containsKey(targetInBoogieVar)){
				TermVariable t_invar	= target_inVars.get(targetInBoogieVar);
				TermVariable e_outvar	= edge_outVars.get(targetInBoogieVar);
				addSubstitution(t_invar, e_outvar);
//				if(subTermMapping.put(t_invar, e_outvar) != null) {
//					throw new UnknownError("Overriding value for substitution!");
//				}
//				target_assertion = s_subTermTransformer.substitute(target_assertion, t_invar, e_outvar);
//				target_assertion = m_Script.let(new TermVariable[]{t_invar}, new Term[]{e_outvar}, target_assertion);
				vars.remove(t_invar);
				vars.add(e_outvar);
			} else if (source_inVars.containsKey(targetInBoogieVar)){
				TermVariable t_invar	= target_inVars.get(targetInBoogieVar);
				TermVariable s_invar	= source_inVars.get(targetInBoogieVar);
				addSubstitution(t_invar, s_invar);
//				if(subTermMapping.put(t_invar, s_invar) != null) {
//					throw new UnknownError("Overriding value for substitution!");
//				}
//				target_assertion = s_subTermTransformer.substitute(target_assertion, t_invar, s_invar);
//				target_assertion = m_Script.let(new TermVariable[]{t_invar}, new Term[]{s_invar}, target_assertion);
				vars.remove(t_invar);
			}
		}
//		target_assertion = subTermTransformer.substitute(target_assertion, subTermMapping);
//		subTermMapping.clear();
		
		Term tmp_assertion = negateTarget? Util.not(m_Script, target_assertion): target_assertion;
		
		formula = Util.and(m_Script,  assumption, tmp_assertion);
		
		for (BoogieVar edgeInBoogieVar: edge_inVars.keySet()){
			if (source_inVars.containsKey(edgeInBoogieVar)){
				TermVariable e_invar	= edge_inVars.get(edgeInBoogieVar);
				TermVariable s_invar	= source_inVars.get(edgeInBoogieVar);
				if (e_invar != s_invar){
					addSubstitution(e_invar, s_invar);
//					if(subTermMapping.put(e_invar, s_invar) != null) {
//						throw new UnknownError("Overriding value for substitution!");
//					}
//					formula = s_subTermTransformer.substitute(formula, e_invar, s_invar);
//					formula = m_Script.let(new TermVariable[]{e_invar}, new Term[]{s_invar}, formula);
					vars.remove(e_invar);
				}
			}
		}
//		formula = subTermTransformer.substitute(formula, subTermMapping);
//		subTermMapping.clear();
		
		formula = Util.and(m_Script,  source_assertion, formula);

		//		if (oldVars != null){
//			for (String tName: oldVars.keySet()){
//				TermVariable s_invar = source_inVars.get(tName);
//				if (s_invar != null){
//					formula = m_Script.let(new TermVariable[]{s_invar}, new Term[]{oldVars.get(tName)}, formula);
//					vars.remove(s_invar);
//				}
//			}
//		}

		vars.addAll(source_inVars.values());
		
		TermVariable[] varsArray = new TermVariable[vars.size()];
		vars.toArray(varsArray);
		
		if (varsArray.length > 0) {
			//formula = m_Script.exists(varsArray, formula);
			for (TermVariable tv: varsArray) {
				Term constant = VariableSSAManager.makeConstant(tv);
				addSubstitution(tv, constant);
//				if(subTermMapping.put(tv, constant) != null) {
//					throw new UnknownError("Overriding value for substitution!");
//				}
//				formula = s_subTermTransformer.substitute(formula, tv, constant);
				vars.remove(tv);
//				formula = m_Script.let(new TermVariable[]{tv}, new Term[]{constant}, formula);
			}
		}

//		formula = subTermTransformer.substitute(formula, subTermMapping);
//		subTermMapping.clear();
		
		SubstituteTermTransformer subTermTransformer = new SubstituteTermTransformer();
		formula = subTermTransformer.substitute(formula, m_substitutionMap);
		m_substitutionMap.clear();
		
		if (formula.getFreeVars().length > 0) {
			s_Logger.warn("Free variables " + formula.getFreeVars() + " in formula " + formula);
		}
		
		if (negateTarget) {
			s_Logger.info("Checking validity of edge " + m_Payload.getName()+ ".");
		} else {
			s_Logger.info("Checking satisfiability of edge " + m_Payload.getName()+ ".");
		}
		
		LBool result;
		
		try {
			long startTime = System.currentTimeMillis();
			result = m_SMTInterface.checkSatisfiable(formula);
			s_totalTime += (System.currentTimeMillis() - startTime);
			s_TheoremProverCalls++;
		} catch (SMTLIBException e) {
	    	s_Logger.info("Result: ERROR");
	    	s_Logger.info(e.getMessage());
	    	throw e;
		}
		
		switch (result) {
		case UNSAT:
			s_Logger.info("Result: UNSAT");
		break;
	    case SAT:
	    	s_Logger.info("Result: SAT");
	    break;
	    case UNKNOWN:
	    	s_Logger.info("Result: UNKNOWN");
	    break;
	    default:
	    	s_Logger.info("Result: ERROR");
	    break;
		}	
		return result;
	}
	
//	private Term makeConstant(TermVariable tv){
//		return makeConstant(tv, true);
//	}
	
//	private Term makeConstant(TermVariable tv/*, boolean addConstTag*/){
//		//new name for constant variable
//		String constName = tv.getName() + /*(addConstTag?*/ "_const" /*:"")*/;
//		
//		Term constTerm;
//		if (s_declaredSMTConstants.get(constName) == null) {
//			try {
//				m_Script.declareFun(constName, new Sort[]{}, tv.getSort());
//			} catch (SMTLIBException e) {
//				s_Logger.info(e.getMessage());
//				// Do nothing
//			}
//			constTerm = m_Script.term(constName);
//			s_declaredSMTConstants.put(constName, constTerm);
//		} else {
//			constTerm = s_declaredSMTConstants.get(constName);
//		}
//		
//		return constTerm;
//	}
	
	public void addIdentityAlternative() {
		Term identity = m_Script.term("true");
		SMTEdgeAnnotations				annotation	= getSMTAnnotations();
		HashMap<BoogieVar, TermVariable>	inVars		= annotation.getInVars();
		HashSet<TermVariable>			vars		= annotation.getVars();
		HashMap<BoogieVar, TermVariable>	outVars		= annotation.getOutVars();
		Term							assumption	= annotation.getAssumption();
		
		for (BoogieVar outBoogieVar: outVars.keySet()) {
			TermVariable invar = inVars.get(outBoogieVar);
			TermVariable outvar = outVars.get(outBoogieVar);
			if (invar != null){
				if (invar != outvar) {
					identity = Util.and(m_Script,  identity, m_Script.term("=", outvar, invar));
				} else {
					TermVariable newOutvar = VariableSSAManager.getFreshTermVariable(outBoogieVar, outvar.getSort());
					Term equals = m_Script.term("=", newOutvar, invar);
					outVars.put(outBoogieVar, newOutvar);
					vars.add(newOutvar);
					identity = Util.and(m_Script,  identity, equals);
					assumption = Util.and(m_Script,  assumption, equals);
				}
			} else {
				TermVariable newInvar = VariableSSAManager.getFreshTermVariable(outBoogieVar, outvar.getSort());
				Term equals = m_Script.term("=", outvar, newInvar);
				inVars.put(outBoogieVar, newInvar);
				vars.add(newInvar);
				identity = Util.and(m_Script,  identity, equals);
			}
		}
		assumption = Util.or(m_Script, assumption, identity);
		annotation.setInVars(inVars);
		annotation.setVars(vars);
		annotation.setOutVars(outVars);
		annotation.setAssumption(assumption);
	}
	
	public String toString(){
		return getPayload().getName();
	}
	
	@Override
	public List<IWalkable> getSuccessors() {
		return Collections.singletonList((IWalkable) m_Target);
	}
}