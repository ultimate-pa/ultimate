package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;

public class RelevantVariables {

	public final TraceWithFormulas<TransFormula> m_TraceWithFormulas;
	public final Set<BoogieVar>[] m_ForwardRelevantVariables;
	
	@SuppressWarnings("unchecked")
	public RelevantVariables(TraceWithFormulas<TransFormula> traceWithFormulas) {
		super();
		m_TraceWithFormulas = traceWithFormulas;
		m_ForwardRelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeForwardRelevantVariables();
	}
	
	public Set<BoogieVar>[] getForwardRelevantVariables() {
		return m_ForwardRelevantVariables;
	}

	private void computeForwardRelevantVariables() {
		assert m_ForwardRelevantVariables[0] == null : "already computed";
		m_ForwardRelevantVariables[0] = Collections.emptySet();
		for (int i=1; i<=m_TraceWithFormulas.getTrace().length(); i++) {
			assert m_ForwardRelevantVariables[i] == null : "already computed";
			m_ForwardRelevantVariables[i] = computeForwardRelevantVariables(i);
		}
	}
	
	private Set<BoogieVar> computeForwardRelevantVariables(int i) {
		Set<BoogieVar> result;
		Set<BoogieVar> currentRelevantVariables = m_ForwardRelevantVariables[i-1];
		if (m_TraceWithFormulas.getTrace().isInternalPosition(i-1)) {
			TransFormula tf = m_TraceWithFormulas.getFormulaFromNonCallPos(i-1);
			result = computeSuccessorRvInternal(currentRelevantVariables,tf);
		} else if (m_TraceWithFormulas.getTrace().isCallPosition(i-1)) {
			TransFormula oldVarAssignment =m_TraceWithFormulas.getOldVarAssignment(i-1);
			TransFormula localVarAssignment =m_TraceWithFormulas.getLocalVarAssignment(i-1);
			result = computeSuccessorRvCall(currentRelevantVariables, 
					localVarAssignment, oldVarAssignment);
		} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i-1)) {
			int correspondingCallPosition = m_TraceWithFormulas.getTrace().getCallPosition(i-1);
			Set<BoogieVar> relevantVariablesBeforeCall = 
					m_ForwardRelevantVariables[correspondingCallPosition];
			TransFormula tfReturn = m_TraceWithFormulas.getFormulaFromNonCallPos(i-1);
			result = computeSuccessorRvReturn(currentRelevantVariables, 
					relevantVariablesBeforeCall, tfReturn);
		} else {
			throw new AssertionError();
		}
		return result;
	}
	
	private Set<BoogieVar> computeSuccessorRvInternal(Set<BoogieVar> predRv, TransFormula tf) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(predRv.size());
		for (BoogieVar bv : predRv) {
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
	
	private Set<BoogieVar> computeSuccessorRvCall(Set<BoogieVar> predRv, 
			TransFormula localVarAssignment, TransFormula oldVarAssignment) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(predRv.size());
		for (BoogieVar bv : predRv) {
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
	
	
	private Set<BoogieVar> computeSuccessorRvReturn(Set<BoogieVar> returnPredRv,
			Set<BoogieVar> callPredRv,
			TransFormula localVarAssignment) {
		// add all vars that were relevant before the call
		Set<BoogieVar> result = new HashSet<BoogieVar>(callPredRv);
		// add all global vars that are relevant before the return
		for (BoogieVar bv : returnPredRv) {
			if (bv.isGlobal()) {
				result.add(bv);
			}
		}
		// add all vars that are assigned by the call
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
			return !Arrays.asList(tf.getFormula().getFreeVars()).contains(tf.getOutVars().get(bv)); 
		}
	}

}
