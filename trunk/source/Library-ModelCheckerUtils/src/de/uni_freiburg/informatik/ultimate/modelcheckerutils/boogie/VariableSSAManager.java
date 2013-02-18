package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

public class VariableSSAManager {

	static HashMap<BoogieVar, Integer> s_VariableIndexMap = new HashMap<BoogieVar, Integer>();
	static HashMap<TermVariable, BoogieVar> s_Variable2BoogieVarMap = new HashMap<TermVariable, BoogieVar>();
	static HashMap<TermVariable, Term> s_declaredSMTConstants = new HashMap<TermVariable, Term>();
	static Script s_Script = null;
	
	public VariableSSAManager(Script script) {
		s_Script = script;
	}
	
	private static int getNextVariableIndex(BoogieVar boogieVariable) {
		return getVariableIndex(boogieVariable, true);
	}
	
	public static TermVariable getFreshTermVariable(BoogieVar boogieVariable, Sort sort) {
		TermVariable result = s_Script.variable("v_" + boogieVariable.getIdentifier() + "_" +
				getNextVariableIndex(boogieVariable), sort);
		s_Variable2BoogieVarMap.put(result, boogieVariable);
		return result;
	}
	
	public static TermVariable getFutureTermVariable(BoogieVar boogieVariable, Sort sort) {
		TermVariable result = s_Script.variable("v_" + boogieVariable.getIdentifier() + "_" +
				(getVariableIndex(boogieVariable, false)+1), sort);
		s_Variable2BoogieVarMap.put(result, boogieVariable);
		return result;
	}
	
	public static TermVariable getFreshTermVariable(TermVariable termVariable) {
		BoogieVar boogieVariable = s_Variable2BoogieVarMap.get(termVariable);
		Sort sort = termVariable.getSort();
		int index = getNextVariableIndex(boogieVariable);
		TermVariable result =  s_Script.variable("v_" + boogieVariable.getIdentifier() + "_" + index, sort);
		s_Variable2BoogieVarMap.put(result, boogieVariable);
		return result;
	}
	
	public static BoogieVar getBoogieVariable(TermVariable termVariable) {
		return s_Variable2BoogieVarMap.get(termVariable);
	}
	
	public static void incAllIndices() {
		for(BoogieVar boogieVar: s_VariableIndexMap.keySet()) {
			s_VariableIndexMap.put(boogieVar, s_VariableIndexMap.get(boogieVar) + 1);
		}
	}
	
	private static int getVariableIndex(BoogieVar boogieVariable, boolean incrementIndex) {
		Integer result;
		if(s_VariableIndexMap.containsKey(boogieVariable)) {
			result = s_VariableIndexMap.get(boogieVariable);
		} else {
			result = -1;
		}
		if (incrementIndex) s_VariableIndexMap.put(boogieVariable, ++result);
		return result;
	}
	
	public static Term makeConstant(TermVariable tv/*, boolean addConstTag*/){
		//new name for constant variable
		String constName = tv.getName() + /*(addConstTag?*/ "_const" /*:"")*/;
		
		Term constTerm;
		constTerm = s_declaredSMTConstants.get(tv);
		if (constTerm == null) {
			constTerm = makeConstant(constName, tv.getSort());
			s_declaredSMTConstants.put(tv, constTerm);
		}
		
		return constTerm;
	}
	
	public static Term makeConstant(String name, Sort sort) {
		try {
			s_Script.declareFun(name, new Sort[]{}, sort);
		} catch (SMTLIBException e) {
			throw e;
		}
		return s_Script.term(name);
	}
	
	public void reset() {
		s_declaredSMTConstants.clear();
		s_Variable2BoogieVarMap.clear();
		s_VariableIndexMap.clear();
	}
}
