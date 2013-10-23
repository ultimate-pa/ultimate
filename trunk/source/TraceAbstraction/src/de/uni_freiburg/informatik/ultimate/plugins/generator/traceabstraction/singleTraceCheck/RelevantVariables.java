package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;


/**
 * TODO: documentation, support for pending contexts
 * 
 * @author Matthias Heizmann
 *
 */
public class RelevantVariables {

	public final NestedFormulas<TransFormula, IPredicate> m_TraceWithFormulas;
	public final Set<BoogieVar>[] m_ForwardRelevantVariables;
	public final Set<BoogieVar>[] m_BackwardRelevantVariables;
	public final Set<BoogieVar>[] m_RelevantVariables;
	

	public RelevantVariables(NestedFormulas<TransFormula, IPredicate> traceWithFormulas) {
		super();
		m_TraceWithFormulas = traceWithFormulas;
		m_ForwardRelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeForwardRelevantVariables();
		m_BackwardRelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeBackwardRelevantVariables();
		m_RelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeRelevantVariables();
	}
	
	public Set<BoogieVar>[] getForwardRelevantVariables() {
		return m_ForwardRelevantVariables;
	}

	public Set<BoogieVar>[] getBackwardRelevantVariables() {
		return m_BackwardRelevantVariables;
	}

	public Set<BoogieVar>[] getRelevantVariables() {
		return m_RelevantVariables;
	}

	private void computeRelevantVariables() {
		for (int i=0; i<=m_TraceWithFormulas.getTrace().length(); i++) {
			m_RelevantVariables[i] = new HashSet<BoogieVar>(m_ForwardRelevantVariables[i]);
			m_RelevantVariables[i].retainAll(m_BackwardRelevantVariables[i]);
		}
	}
	

	private void computeForwardRelevantVariables() {
		assert m_ForwardRelevantVariables[0] == null : "already computed";
		m_ForwardRelevantVariables[0] = 
				new HashSet<BoogieVar>(m_TraceWithFormulas.getPrecondition().getVars());
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
			TransFormula oldVarAssignment = m_TraceWithFormulas.getOldVarAssignment(i-1);
			TransFormula localVarAssignment = m_TraceWithFormulas.getLocalVarAssignment(i-1);
			result = computeSuccessorRvCall(currentRelevantVariables, 
					localVarAssignment, oldVarAssignment);
		} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i-1)) {
			int correspondingCallPosition = m_TraceWithFormulas.getTrace().getCallPosition(i-1);
			Set<BoogieVar> relevantVariablesBeforeCall = 
					m_ForwardRelevantVariables[correspondingCallPosition];
			TransFormula tfReturn = m_TraceWithFormulas.getFormulaFromNonCallPos(i-1);
			TransFormula localVarAssignmentAtCall = 
					m_TraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			result = computeSuccessorRvReturn(currentRelevantVariables, 
					relevantVariablesBeforeCall, tfReturn, localVarAssignmentAtCall);
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
			TransFormula returnTF, TransFormula localVarAssignment) {
		// add all vars that were relevant before the call
		Set<BoogieVar> result = new HashSet<BoogieVar>(callPredRv);
		// add all global vars that are relevant before the return
		for (BoogieVar bv : returnPredRv) {
			if (bv.isGlobal()) {
				result.add(bv);
			}
		}
		// add all vars that are assigned by the call
		for (BoogieVar bv : returnTF.getOutVars().keySet()) {
			result.add(bv);
		}
		// add all arguments of the call
		for (BoogieVar bv : localVarAssignment.getInVars().keySet()) {
			result.add(bv);
		}
		return result;
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	private void computeBackwardRelevantVariables() {
		assert m_BackwardRelevantVariables[m_TraceWithFormulas.getTrace().length()] == null : "already computed";
		m_BackwardRelevantVariables[m_TraceWithFormulas.getTrace().length()] = 
				new HashSet<BoogieVar>(m_TraceWithFormulas.getPostcondition().getVars());
		for (int i=m_TraceWithFormulas.getTrace().length()-1; i>=0; i--) {
			assert m_BackwardRelevantVariables[i] == null : "already computed";
			m_BackwardRelevantVariables[i] = computeBackwardRelevantVariables(i);
		}
	}
	
	private Set<BoogieVar> computeBackwardRelevantVariables(int i) {
		Set<BoogieVar> result;
		Set<BoogieVar> currentRelevantVariables = m_BackwardRelevantVariables[i+1];
		if (m_TraceWithFormulas.getTrace().isInternalPosition(i)) {
			TransFormula tf = m_TraceWithFormulas.getFormulaFromNonCallPos(i);
			result = computePredecessorRvInternal(currentRelevantVariables,tf);
		} else if (m_TraceWithFormulas.getTrace().isCallPosition(i)) {
			TransFormula localVarAssignment = m_TraceWithFormulas.getLocalVarAssignment(i);
			if (m_TraceWithFormulas.getTrace().isPendingCall(i)) {
				result = computePredecessorRvCall_Pending(currentRelevantVariables, localVarAssignment);
			} else {
				int correspondingReturnPosition = m_TraceWithFormulas.getTrace().getReturnPosition(i);
				Set<BoogieVar> relevantVariablesAfterReturn = 
						m_BackwardRelevantVariables[correspondingReturnPosition+1];
				result = computePredecessorRvCall_NonPending(currentRelevantVariables, 
						relevantVariablesAfterReturn, localVarAssignment);
				addNonModifiableGlobalsAlongCalledProcedure(result,i);
			}
		} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i)) {
			int correspondingCallPosition = m_TraceWithFormulas.getTrace().getCallPosition(i);
			TransFormula oldVarAssignment =m_TraceWithFormulas.getOldVarAssignment(correspondingCallPosition);
			TransFormula localVarAssignment =m_TraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			TransFormula tfReturn = m_TraceWithFormulas.getFormulaFromNonCallPos(i);
			result = computePredecessorRvReturn(currentRelevantVariables, 
					tfReturn, oldVarAssignment, localVarAssignment);
		} else {
			throw new AssertionError();
		}
		return result;
	}
	
	/**
	 * Relevant variables directly before the call that are global are also 
	 * relevant during the whole procedure. Variables that are modifiable by the
	 * procedure (and corresponding oldvars) have already been added (we have
	 * to add the others.  
	 */
	private void addNonModifiableGlobalsAlongCalledProcedure(
			Set<BoogieVar> relevantVariablesBeforeCall, int i) {
		assert m_TraceWithFormulas.getTrace().isCallPosition(i);
		assert !m_TraceWithFormulas.getTrace().isPendingCall(i);
		Set<BoogieVar> modifiableGlobals = 
				m_TraceWithFormulas.getGlobalVarAssignment(i).getOutVars().keySet();
		Set<BoogieVar> oldVarsOfModifiableGlobals = 
				m_TraceWithFormulas.getGlobalVarAssignment(i).getOutVars().keySet();
		Set<BoogieVar> varsThatWeHaveToAdd = new HashSet<BoogieVar>();
		for (BoogieVar bv : relevantVariablesBeforeCall) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (!oldVarsOfModifiableGlobals.contains(bv)) {
						varsThatWeHaveToAdd.add(bv);
					}
				} else {
					if (!modifiableGlobals.contains(bv)) {
						varsThatWeHaveToAdd.add(bv);
					}
				}
			}
		}
		if (!varsThatWeHaveToAdd.isEmpty()) {
			int returnPosition = m_TraceWithFormulas.getTrace().getReturnPosition(i);
			for (int pos = i+1; pos<=returnPosition; pos++) {
				m_BackwardRelevantVariables[pos].addAll(varsThatWeHaveToAdd);
			}
		}
	}

	private Set<BoogieVar> computePredecessorRvInternal(Set<BoogieVar> succRv, TransFormula tf) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(succRv.size());
		for (BoogieVar bv : succRv) {
			if (!isHavoced(bv,tf)) {
				result.add(bv);
			}
		}
		if (true || containsSomeNonHavocedOutVar(succRv, tf)) {
			result.addAll(tf.getInVars().keySet());
		}
		return result;
	}
	
	private boolean containsSomeNonHavocedOutVar(Set<BoogieVar> bvs, TransFormula tf) {
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (!isHavoced(bv, tf) &&  bvs.contains(bv)) {
				return true;
			}
		}
		return false;
	}
	
	private Set<BoogieVar> computePredecessorRvCall_NonPending(Set<BoogieVar> callPredRv, 
			Set<BoogieVar> returnPredRv,
			TransFormula localVarAssignment) {
		Set<BoogieVar> result = new HashSet<BoogieVar>();
		result.addAll(returnPredRv);
		result.addAll(localVarAssignment.getInVars().keySet());
		for (BoogieVar bv : callPredRv) {
			if (bv.isGlobal()) {
				result.add(bv);
			}
		}
		return result;
	}
	
	private Set<BoogieVar> computePredecessorRvCall_Pending(Set<BoogieVar> callPredRv,
			TransFormula localVarAssignment) {
		Set<BoogieVar> result = new HashSet<BoogieVar>();
		result.addAll(localVarAssignment.getInVars().keySet());
		for (BoogieVar bv : callPredRv) {
			if (bv.isGlobal()) {
				result.add(bv);
			}
		}
		
		return result;
	}
	
	
	private Set<BoogieVar> computePredecessorRvReturn(Set<BoogieVar> returnSuccRv,
			TransFormula returnTf,
			TransFormula oldVarAssignmentAtCall, TransFormula localVarAssignmentAtCall) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(returnSuccRv.size());
		for (BoogieVar bv : returnSuccRv) {
			if (bv.isGlobal()) {
				result.add(bv);
			} else {
				//do nothing
			}
		}
		if (true || containsSomeNonHavocedOutVar(returnSuccRv, returnTf)) {
			result.addAll(returnTf.getInVars().keySet());
		}
		result.addAll(oldVarAssignmentAtCall.getInVars().keySet());
		result.addAll(oldVarAssignmentAtCall.getOutVars().keySet());
		
		result.addAll(localVarAssignmentAtCall.getOutVars().keySet());
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
