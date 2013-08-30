package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;

public class RelevantVariables {
	
	public final NestedWord<CodeBlock> m_Trace;
	public final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	public final Set<BoogieVar>[] m_ForwardRelevantVariables;
	
	
	

	public RelevantVariables(NestedWord<CodeBlock> trace,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager) {
		super();
		m_Trace = trace;
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_ForwardRelevantVariables = computeForwardRelevantVariables();
	}

	private Set<BoogieVar>[] computeForwardRelevantVariables() {
		Set<BoogieVar>[] result = new Set[m_Trace.length()+1];
		result[0] = Collections.emptySet();
		
		return result;
		
		
	}
	
	private Set<BoogieVar> computeForwardRelevantVariables(int i) {
		Set<BoogieVar> result;
		Set<BoogieVar> currentRelevantVariables = m_ForwardRelevantVariables[i];
		if (m_Trace.isInternalPosition(i)) {
			result = computeSuccessorRVInternal(currentRelevantVariables, m_Trace.getSymbol(i).getTransitionFormula());
		} else if (m_Trace.isCallPosition(i)) {
			Call call = (Call) m_Trace.getSymbol(i);
			m_ModifiableGlobalVariableManager.getOldVarsAssignment(call.getCallStatement().getMethodName());
			result = null;
		} else if (m_Trace.isReturnPosition(i)) {
			result = null;
		} else {
			throw new AssertionError();
		}
		return result;
	}
	
	private Set<BoogieVar> computeSuccessorRVInternal(Set<BoogieVar> rvs, TransFormula tf) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(rvs.size());
		for (BoogieVar bv : rvs) {
			if (!isHavoced(bv,tf)) {
				result.add(bv);
			}
		}
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (!isHavoced(bv,tf)) {
				result.add(bv);
			}
			
		}
		return result;
	}
	
	private Set<BoogieVar> computeSuccessorRVCall(Set<BoogieVar> rvs, 
			TransFormula localVarAssignment, TransFormula oldVarAssignment) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(rvs.size());
		for (BoogieVar bv : rvs) {
			if (bv.isGlobal() && !oldVarAssignment.getInVars().containsKey(bv)) {
				// is global var that can not be modfied by called procedure
				result.add(bv);
			}
		}
		for (BoogieVar bv : oldVarAssignment.getInVars().keySet()) {
			result.add(bv);
		}
		for (BoogieVar bv : oldVarAssignment.getOutVars().keySet()) {
			result.add(bv);
		}
		for (BoogieVar bv : localVarAssignment.getOutVars().keySet()) {
			result.add(bv);
		}
		return result;
	}	
	
	
	
	/**
	 * Return true if this TransFormula modifies the BoogieVar bv, but after
	 * executing the TransFormula every value of bv is possible. This is the 
	 * case for a variable x and the TransFormula of the statement havoc x.
	 */
	private boolean isHavoced(BoogieVar bv, TransFormula tf) {
		TermVariable outVar = tf.getOutVars().get(bv);
		if (outVar == null) {
			return false;
		} else {
			return !Arrays.asList(tf.getFormula().getFreeVars()).contains(bv);
		}
	}

}
