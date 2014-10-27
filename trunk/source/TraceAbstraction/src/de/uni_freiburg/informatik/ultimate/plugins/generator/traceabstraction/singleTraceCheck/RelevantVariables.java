package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.GlobalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.RelationWithTreeSet;


/**
 * TODO: documentation, support for pending contexts
 * 
 * @author Matthias Heizmann
 *
 */
public class RelevantVariables {

	private final NestedFormulas<TransFormula, IPredicate> m_TraceWithFormulas;
	private final Set<BoogieVar>[] m_ForwardRelevantVariables;
	private final Set<BoogieVar>[] m_BackwardRelevantVariables;
	private final Set<BoogieVar>[] m_RelevantVariables;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;
	private final NestedConstraintAnalysis m_NestedConstraintAnalysis;
	private VariableOccurrence m_Occurrence;
	

	public RelevantVariables(NestedFormulas<TransFormula, IPredicate> traceWithFormulas, 
			ModifiableGlobalVariableManager modifiedGlobals) {
		super();
		m_ModifiableGlobals = modifiedGlobals;
		m_TraceWithFormulas = traceWithFormulas;
		m_NestedConstraintAnalysis = new NestedConstraintAnalysis(traceWithFormulas.getTrace(), new TreeMap<Integer, IPredicate>(), traceWithFormulas);
		m_Occurrence = new VariableOccurrence();
		m_ForwardRelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeForwardRelevantVariables();
		m_BackwardRelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeBackwardRelevantVariables();
		m_RelevantVariables = new Set[m_TraceWithFormulas.getTrace().length()+1];
		computeRelevantVariables();
//		assert checkRelevantVariables();
	}
	
	/**
	 * Check if the sets of relevant variables are not too large.
	 * Each relevant variable has to occur before and after position i.
	 */
	private boolean checkRelevantVariables() {
		boolean result = true;
		for (int i=0; i<m_TraceWithFormulas.getTrace().length(); i++) {
			Set<BoogieVar> relevantVars = m_RelevantVariables[i+1];
			for (BoogieVar bv : relevantVars) {
				result &= m_Occurrence.occursBefore(bv, i);
				assert result : "superfluous variable";
				result &= m_Occurrence.occursAfter(bv, i);
				assert result : "superfluous variable";
			}
		}
		return result;
	}

	/**
	 * Efficient data structure that stores where variable occurs.
	 * Stores this separately for "in" and "out".
	 * Precondition gets index -1.
	 * Postcondition gets index trace.length()
	 *
	 */
	private class VariableOccurrence {
		RelationWithTreeSet<BoogieVar, Integer> inRelation = new RelationWithTreeSet();
		RelationWithTreeSet<BoogieVar, Integer> outRelation = new RelationWithTreeSet();
		
		public VariableOccurrence() {
			computeOccurrenceRelations();
		}
		
		/**
		 * Returns true iff set contains number between lower and upper 
		 * (inclusive lower, inclusive upper).
		 */
		public boolean containsNumberBetween(int lower, int upper, TreeSet<Integer> set) {
			Integer ceiling = set.ceiling(lower);
			if (ceiling == null) {
				return false;
			} else {
				return ceiling <= upper;
			}
		}
		
		public boolean occurs(BoogieVar bv, int start, int end) {
			boolean result = false;
			TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			result = result || containsNumberBetween(start+1, end, inSet);
			if (result == true) {
				return result;
			}
			TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			result = result || containsNumberBetween(start, end-1, outSet);
			return result;
		}
		
		public boolean occursAfter(BoogieVar bv, int start) {
			boolean result = false;
			TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			result = result || inSet.ceiling(start+1) != null;
			if (result == true) {
				return result;
			}
			TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			result = result ||  outSet.ceiling(start) != null;
			return result;
		}
		
		public boolean occursBefore(BoogieVar bv, int end) {
			boolean result = false;
			TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			result = result || inSet.floor(end) != null;
			if (result == true) {
				return result;
			}
			TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			result = result ||  outSet.ceiling(end-1) != null;
			return result;
		}

	
		private void computeOccurrenceRelations() {
			addVars(outRelation, -1, m_TraceWithFormulas.getPrecondition());
			addVars(inRelation, m_TraceWithFormulas.getTrace().length(), m_TraceWithFormulas.getPostcondition());
			for (int i=0; i<m_TraceWithFormulas.getTrace().length(); i++) {
				if (m_TraceWithFormulas.getTrace().isInternalPosition(i)) {
					ConstraintAnalysis ca = m_NestedConstraintAnalysis.getFormulaFromNonCallPos(i);
					addVars(inRelation, i, ca.getConstraintIn());
					addVars(outRelation, i, ca.getConstraintOut());
				} else if (m_TraceWithFormulas.getTrace().isCallPosition(i)) {
					ConstraintAnalysis localVarAssignment = m_NestedConstraintAnalysis.getLocalVarAssignment(i);
					ConstraintAnalysis oldVarAssignment = m_NestedConstraintAnalysis.getOldVarAssignment(i);
					ConstraintAnalysis globalVarAssignment = m_NestedConstraintAnalysis.getGlobalVarAssignment(i);
					addVars(inRelation, i, localVarAssignment.getConstraintIn());
					addVars(inRelation, i, oldVarAssignment.getConstraintIn());
					addVars(outRelation, i, globalVarAssignment.getConstraintOut());

					if (m_TraceWithFormulas.getTrace().isPendingCall(i)) {
						addVars(inRelation, i, oldVarAssignment.getConstraintIn());
						addVars(outRelation, i, localVarAssignment.getConstraintOut());
					} else {
						// nothing more. The return has to take care of it
					}
				} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i)) {
					int correspondingCallPosition = m_NestedConstraintAnalysis.getTrace().getCallPosition(i);
					ConstraintAnalysis oldVarAssignment = m_NestedConstraintAnalysis.getOldVarAssignment(correspondingCallPosition);
					ConstraintAnalysis localVarAssignment = m_NestedConstraintAnalysis.getLocalVarAssignment(correspondingCallPosition);
					ConstraintAnalysis tfReturn = m_NestedConstraintAnalysis.getFormulaFromNonCallPos(i);

					//outVars from call become members of inRelation here
					addVars(inRelation, i, localVarAssignment.getConstraintOut());
					addVars(inRelation, i, oldVarAssignment.getConstraintOut());
					addVars(inRelation, i, tfReturn.getConstraintIn());
					addVars(outRelation, i, tfReturn.getConstraintOut());
				} else {
					throw new AssertionError();
				}
			}

		}

		private void addVars(
				RelationWithTreeSet<BoogieVar, Integer> relation, int i,
				IPredicate precondition) {
			for (BoogieVar bv : precondition.getVars()) {
				relation.addPair(bv, i);
			}

		}
		
		private void addVars(
				RelationWithTreeSet<BoogieVar, Integer> relation, int i,
				Set<BoogieVar> set) {
			for (BoogieVar bv : set) {
				relation.addPair(bv, i);
			}
		}
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
			result = computeSuccessorRvInternal(currentRelevantVariables, tf, i-1);
		} else if (m_TraceWithFormulas.getTrace().isCallPosition(i-1)) {
			TransFormula oldVarAssignment = m_TraceWithFormulas.getOldVarAssignment(i-1);
			TransFormula localVarAssignment = m_TraceWithFormulas.getLocalVarAssignment(i-1);
			TransFormula globalVarAssignment = m_TraceWithFormulas.getGlobalVarAssignment(i-1);
			String callee = m_TraceWithFormulas.getTrace().getSymbol(i-1).getSucceedingProcedure();
			boolean isPendingCall = m_TraceWithFormulas.getTrace().isPendingCall(i-1);
			int posOfCorrespondingReturn = m_TraceWithFormulas.getTrace().getReturnPosition(i-1);
			result = computeSuccessorRvCall(currentRelevantVariables, 
					localVarAssignment, oldVarAssignment, globalVarAssignment, isPendingCall, callee, i-1, posOfCorrespondingReturn);
		} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i-1)) {
			int correspondingCallPosition = m_TraceWithFormulas.getTrace().getCallPosition(i-1);
			Set<BoogieVar> relevantVariablesBeforeCall = 
					m_ForwardRelevantVariables[correspondingCallPosition];
			TransFormula tfReturn = m_TraceWithFormulas.getFormulaFromNonCallPos(i-1);
			TransFormula localVarAssignmentAtCall = 
					m_TraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			String callee = m_TraceWithFormulas.getTrace().getSymbol(i-1).getPreceedingProcedure();
			result = computeSuccessorRvReturn(currentRelevantVariables, 
					relevantVariablesBeforeCall, tfReturn, localVarAssignmentAtCall, callee, correspondingCallPosition, i-1);
		} else {
			throw new AssertionError();
		}
		return result;
	}
	
	private Set<BoogieVar> computeSuccessorRvInternal(Set<BoogieVar> predRv, TransFormula tf, int i) {
		Set<BoogieVar> result = new HashSet<BoogieVar>(predRv.size());
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>(predRv);
		ConstraintAnalysis tfConstraints = 
				m_NestedConstraintAnalysis.getFormulaFromNonCallPos(i);
		alternativeResult.removeAll(tfConstraints.getUnconstraintOut());
		alternativeResult.addAll(tfConstraints.getConstraintOut());
		
		for (BoogieVar bv : predRv) {
			if (!tf.isHavocedOut(bv)) {
				result.add(bv);
			}
		}
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (!tf.isHavocedOut(bv)) {
				result.add(bv);
			}
			
		}
		assert result.equals(alternativeResult) : "not equal";
		return result;
	}
	
	private Set<BoogieVar> computeSuccessorRvCall(Set<BoogieVar> predRv, 
			TransFormula localVarAssignment, TransFormula oldVarAssignment, 
			TransFormula globalVarAssignment, boolean isPendingCall,
			String callee, int posOfCall, int posOfCorrespondingReturn) {
		assert !isPendingCall || posOfCorrespondingReturn == Integer.MAX_VALUE;
		Set<BoogieVar> result = new HashSet<BoogieVar>(predRv.size());
		addAllNonModifiableGlobals(predRv, callee, posOfCall,
				posOfCorrespondingReturn, result);

		ConstraintAnalysis globalVarAssignmentCa = 
				m_NestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);
		result.addAll(globalVarAssignmentCa.getConstraintOut());
		if (isPendingCall) {
			ConstraintAnalysis localVarAssignmentCa = 
					m_NestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
			result.addAll(localVarAssignmentCa.getConstraintOut());
			
//			for (BoogieVar bv : oldVarAssignment.getInVars().keySet()) {
//				result.add(bv);
//			}
//			for (BoogieVar bv : oldVarAssignment.getOutVars().keySet()) {
//				result.add(bv);
//			}
//			for (BoogieVar bv : localVarAssignment.getOutVars().keySet()) {
//				result.add(bv);
//			}
		}
		return result;
	}

	private void addAllNonModifiableGlobals(Set<BoogieVar> bvSet, String proc,
			int startPos, int endPos, Set<BoogieVar> modifiedSet) {
		for (BoogieVar bv : bvSet) {
			if (bv.isGlobal()) {
				BoogieNonOldVar bnov;
				if (bv instanceof BoogieOldVar) {
					bnov = ((BoogieOldVar) bv).getNonOldVar();
				} else {
					bnov = (BoogieNonOldVar) bv;
				}
				if (!m_ModifiableGlobals.isModifiable(bnov, proc)) {
					if (occursBetween(bnov, startPos, endPos)) {
						modifiedSet.add(bnov);
					}
				}
			}
		}
	}
	
	private void addAllNonModifiableGlobals(Set<BoogieVar> bvSet, String proc, 
			Set<BoogieVar> modifiedSet) {
		for (BoogieVar bv : bvSet) {
			if (bv.isGlobal()) {
				BoogieNonOldVar bnov;
				if (bv instanceof BoogieOldVar) {
					bnov = ((BoogieOldVar) bv).getNonOldVar();
				} else {
					bnov = (BoogieNonOldVar) bv;
				}
				if (!m_ModifiableGlobals.isModifiable(bnov, proc)) {
					modifiedSet.add(bv);
				}
			}
		}
	}
	
	
	private boolean occursBetween(BoogieVar bv, int lower, int upper) {
//		return true;
		return m_Occurrence.occurs(bv, lower, upper);
	}

	private Set<BoogieVar> computeSuccessorRvReturn(Set<BoogieVar> returnPredRv,
			Set<BoogieVar> callPredRv,
			TransFormula returnTF, TransFormula localVarAssignment,
			String callee, int posOfCall, int posOfCorrespondingReturn) {
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>(callPredRv);
		ConstraintAnalysis localVarAssignmentCa = 
				m_NestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		ConstraintAnalysis returnTfCa = 
				m_NestedConstraintAnalysis.getFormulaFromNonCallPos(posOfCorrespondingReturn);
		ConstraintAnalysis oldVarAssignmentCa = 
				m_NestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		
		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());
		// remove all globals that can be modified
		Iterator<BoogieVar> it = alternativeResult.iterator();
		while(it.hasNext()) {
			BoogieVar bv = it.next();
			if (bv instanceof BoogieNonOldVar) {
				if (m_ModifiableGlobals.isModifiable((BoogieNonOldVar) bv, callee)) {
					it.remove();
				}
			}
		}
		alternativeResult.removeAll(returnTfCa.getUnconstraintOut());
//		alternativeResult.addAll(oldVarAssignmentCa.getConstraintOut());
		// add all global vars cannot be modified by the callee -- NO! add all global nonOld vars!
		for (BoogieVar bv : returnPredRv) {
			if (bv instanceof BoogieNonOldVar) {
				alternativeResult.add(bv);
			}
//			if (bv.isGlobal()) {
//				BoogieNonOldVar bnov;
//				if (bv instanceof BoogieOldVar) {
//					bnov = ((BoogieOldVar) bv).getNonOldVar();
//				} else {
//					bnov = (BoogieNonOldVar) bv;
//				}
//				if (!m_ModifiableGlobals.isModifiable(bnov, callee)) {
//					alternativeResult.add(bv);
//				}
//			}
		}
		alternativeResult.addAll(returnTfCa.getConstraintOut());
		
		
		// add all vars that were relevant before the call
		Set<BoogieVar> result = new HashSet<BoogieVar>();
		
		for (BoogieVar bv : callPredRv) {
			if (!returnTF.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
		
		// add all global vars that are relevant before the return
		for (BoogieVar bv : returnPredRv) {
			if (bv.isGlobal()) {
				if (!returnTF.isHavocedOut(bv) && true) {
					result.add(bv);
				}
			}
		}
		// add all vars that are assigned by the call
		for (BoogieVar bv : returnTF.getOutVars().keySet()) {
			if (!returnTF.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
		// add all arguments of the call
		for (BoogieVar bv : localVarAssignment.getInVars().keySet()) {
			if (!returnTF.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
//		assert alternativeResult.equals(result) : "new rsult ist differtn";
		return alternativeResult;
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
			result = computePredecessorRvInternal(currentRelevantVariables,tf,i);
		} else if (m_TraceWithFormulas.getTrace().isCallPosition(i)) {
			TransFormula localVarAssignment = m_TraceWithFormulas.getLocalVarAssignment(i);
			TransFormula oldVarAssignment = m_TraceWithFormulas.getOldVarAssignment(i);
			TransFormula globalVarAssignment = m_TraceWithFormulas.getGlobalVarAssignment(i);
			String callee = m_TraceWithFormulas.getTrace().getSymbol(i).getSucceedingProcedure();
			if (m_TraceWithFormulas.getTrace().isPendingCall(i)) {
				result = computePredecessorRvCall_Pending(currentRelevantVariables, localVarAssignment, oldVarAssignment, globalVarAssignment, callee, i);
			} else {
				int correspondingReturnPosition = m_TraceWithFormulas.getTrace().getReturnPosition(i);
				Set<BoogieVar> relevantVariablesAfterReturn = 
						m_BackwardRelevantVariables[correspondingReturnPosition+1];
				TransFormula returnTF = m_TraceWithFormulas.getFormulaFromNonCallPos(correspondingReturnPosition);
				result = computePredecessorRvCall_NonPending(currentRelevantVariables, 
						relevantVariablesAfterReturn, localVarAssignment, returnTF, oldVarAssignment, globalVarAssignment, callee, i, correspondingReturnPosition);
				addNonModifiableGlobalsAlongCalledProcedure(result,i);
			}
		} else if (m_TraceWithFormulas.getTrace().isReturnPosition(i)) {
			int correspondingCallPosition = m_TraceWithFormulas.getTrace().getCallPosition(i);
			TransFormula oldVarAssignment =m_TraceWithFormulas.getOldVarAssignment(correspondingCallPosition);
			TransFormula localVarAssignment =m_TraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			TransFormula tfReturn = m_TraceWithFormulas.getFormulaFromNonCallPos(i);
			String callee = m_TraceWithFormulas.getTrace().getSymbol(i).getPreceedingProcedure();
			result = computePredecessorRvReturn(currentRelevantVariables, 
					tfReturn, oldVarAssignment, localVarAssignment, callee, correspondingCallPosition, i);
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
				m_TraceWithFormulas.getOldVarAssignment(i).getOutVars().keySet();
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

	private Set<BoogieVar> computePredecessorRvInternal(Set<BoogieVar> succRv, TransFormula tf, int pos) {
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>(succRv);
		ConstraintAnalysis tfConstraints = 
				m_NestedConstraintAnalysis.getFormulaFromNonCallPos(pos);
		alternativeResult.removeAll(tfConstraints.getUnconstraintIn());
		alternativeResult.addAll(tfConstraints.getConstraintIn());
		
		Set<BoogieVar> result = new HashSet<BoogieVar>(succRv.size());
		for (BoogieVar bv : succRv) {
			if (!tf.isHavocedIn(bv)) {
				result.add(bv);
			}
		}
		for (BoogieVar bv : tf.getInVars().keySet()) {
			if (!tf.isHavocedIn(bv)) {
				result.add(bv);
			}
		}
		assert result.equals(alternativeResult) : "notEqual";
		return result;
	}
	
//	private boolean containsSomeNonHavocedOutVar(Set<BoogieVar> bvs, TransFormula tf) {
//		for (BoogieVar bv : tf.getOutVars().keySet()) {
//			if (!isHavoced(bv, tf) &&  bvs.contains(bv)) {
//				return true;
//			}
//		}
//		return false;
//	}
	
	private Set<BoogieVar> computePredecessorRvCall_NonPending(Set<BoogieVar> callPredRv, 
			Set<BoogieVar> returnPredRv,
			TransFormula localVarAssignment, TransFormula returnTF, 
			TransFormula oldVarAssignment, TransFormula globalVarAssignment, String callee, int posOfCall, int posOfCorrespondingReturn) {
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>(returnPredRv);
		ConstraintAnalysis returnTfCa = 
				m_NestedConstraintAnalysis.getFormulaFromNonCallPos(posOfCorrespondingReturn);
		// remove all that were reassigned
		alternativeResult.removeAll(returnTF.getAssignedVars());
		addAllNonModifiableGlobals(callPredRv, callee, alternativeResult);
		ConstraintAnalysis globalVarAssignmentCa = 
				m_NestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);

		alternativeResult.removeAll(globalVarAssignmentCa.getUnconstraintOut());
		ConstraintAnalysis localVarAssignmentCa = 
				m_NestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());

		// add all (non-old) global vars that are used in the procedure
		ConstraintAnalysis oldVarAssignmentCa = 
				m_NestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		alternativeResult.addAll(oldVarAssignmentCa.getConstraintIn());
		
		
		
		Set<BoogieVar> result = new HashSet<BoogieVar>();
		for (BoogieVar bv : returnPredRv) {
			isHavoced(globalVarAssignment, oldVarAssignment, bv);
			if (!returnTF.isHavocedIn(bv) && !isHavoced(globalVarAssignment, oldVarAssignment, bv)) {
				result.add(bv);
			}
		}
		result.addAll(localVarAssignment.getInVars().keySet());
//		for (BoogieVar bv : callPredRv) {
//			if (bv.isGlobal()) {
//				result.add(bv);
//			}
//		}
		// new
		addAllNonModifiableGlobals(callPredRv, callee, result);
		result.addAll(oldVarAssignment.getInVars().keySet());
//		assert result.equals(alternativeResult) : "notEqual";
		return alternativeResult;
	}
	


	private Set<BoogieVar> computePredecessorRvCall_Pending(Set<BoogieVar> callPredRv,
			TransFormula localVarAssignment, TransFormula oldVarAssignment, TransFormula globalVarAssignment, String callee, int posOfCall) {
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>();
		addAllNonModifiableGlobals(callPredRv, callee, alternativeResult);
		
		ConstraintAnalysis localVarAssignmentCa = 
				m_NestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());
		
		// add all (non-old) global vars that are used in the procedure
		ConstraintAnalysis oldVarAssignmentCa = 
				m_NestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		alternativeResult.addAll(oldVarAssignmentCa.getConstraintIn());
		
		Set<BoogieVar> result = new HashSet<BoogieVar>();
		result.addAll(localVarAssignment.getInVars().keySet());
		for (BoogieVar bv : callPredRv) {
			if (bv.isGlobal()) {
				if (!isHavoced(globalVarAssignment, oldVarAssignment, bv)) {
					result.add(bv);
				}
			}
		}
		
//		assert result.equals(alternativeResult) : "notEqual";
		return alternativeResult;
	}
	
	
	private Set<BoogieVar> computePredecessorRvReturn(Set<BoogieVar> returnSuccRv,
			TransFormula returnTf,
			TransFormula oldVarAssignmentAtCall, TransFormula localVarAssignmentAtCall, String callee, int posOfCorrespondingCall, int posOfReturn) {
		Set<BoogieVar> alternativeResult = new HashSet<BoogieVar>();
		for (BoogieVar bv : returnSuccRv) {
			if (bv instanceof BoogieNonOldVar) {
				if (m_ModifiableGlobals.isModifiable((BoogieNonOldVar) bv, callee)) {
					alternativeResult.add(bv);
				}
			}
		}
		alternativeResult.removeAll(returnTf.getAssignedVars());
		ConstraintAnalysis localVarAssignmentCa = 
				m_NestedConstraintAnalysis.getLocalVarAssignment(posOfCorrespondingCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintOut());
		ConstraintAnalysis returnTfCa = 
				m_NestedConstraintAnalysis.getFormulaFromNonCallPos(posOfReturn);
		alternativeResult.addAll(returnTfCa.getConstraintIn());
		ConstraintAnalysis oldVarAssignmentCa = 
				m_NestedConstraintAnalysis.getOldVarAssignment(posOfCorrespondingCall);
		alternativeResult.addAll(oldVarAssignmentCa.getConstraintOut());
		//FIXME: and remove all globals that are modified???
		
		
		Set<BoogieVar> result = new HashSet<BoogieVar>(returnSuccRv.size());
		for (BoogieVar bv : returnSuccRv) {
			if (bv.isGlobal()) {
				if (!returnTf.isHavocedIn(bv) && true) {
					result.add(bv);
				}
			} else {
				//do nothing
			}
		}
		for (BoogieVar bv : returnTf.getInVars().keySet()) {
			if (!returnTf.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}
		
		for (BoogieVar bv : oldVarAssignmentAtCall.getInVars().keySet()) {
			if (!returnTf.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}
		
		for (BoogieVar bv : oldVarAssignmentAtCall.getOutVars().keySet()) {
			if (!returnTf.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}
		
		for (BoogieVar bv : localVarAssignmentAtCall.getOutVars().keySet()) {
			if (!returnTf.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}
//		assert result.equals(alternativeResult) : "notEqual";
		return alternativeResult;
	}

	
	
	
	
	
	
	private boolean isHavoced(TransFormula globalVarAssignment,
			TransFormula oldVarAssignment, BoogieVar bv) {
		if (bv instanceof GlobalBoogieVar) {
			boolean result;
			if (bv instanceof BoogieOldVar) {
				result = oldVarAssignment.isHavocedOut(bv);
				assert globalVarAssignment.isHavocedOut(((BoogieOldVar) bv).getNonOldVar()) == result : 
					"unexpected: unsat core contains only one of both, globalVarAssignment or oldVarAssignment";
			} else {
				assert (bv instanceof BoogieNonOldVar);
				result = globalVarAssignment.isHavocedOut(bv);
				assert oldVarAssignment.isHavocedOut(((BoogieNonOldVar) bv).getOldVar()) == result  : 
					"unexpected: unsat core contains only one of both, globalVarAssignment or oldVarAssignment";
			}
			return result;
		} else {
			return false;
		}
	}
	
	
	private static class ConstraintAnalysis {
		private final TransFormula m_TransFormula;
		private final Set<BoogieVar> m_ConstraintIn = new HashSet<>();
		private final Set<BoogieVar> m_UnconstraintIn = new HashSet<>();
		private final Set<BoogieVar> m_ConstraintOut = new HashSet<>();
		private final Set<BoogieVar> m_UnconstraintOut = new HashSet<>();
		private final Set<TermVariable> m_FreeVars;
		
		public ConstraintAnalysis(TransFormula transFormula) {
			super();
			this.m_TransFormula = transFormula;
			m_FreeVars = new HashSet<TermVariable>(Arrays.asList(
					transFormula.getFormula().getFreeVars()));
			analyze();
		}
		
		public Set<BoogieVar> getConstraintIn() {
			return m_ConstraintIn;
		}

		public Set<BoogieVar> getUnconstraintIn() {
			return m_UnconstraintIn;
		}

		public Set<BoogieVar> getConstraintOut() {
			return m_ConstraintOut;
		}

		public Set<BoogieVar> getUnconstraintOut() {
			return m_UnconstraintOut;
		}



		private void analyze() {
			for (BoogieVar bv : m_TransFormula.getInVars().keySet()) {
				TermVariable inVar = m_TransFormula.getInVars().get(bv);
				TermVariable outVar = m_TransFormula.getOutVars().get(bv);
				if (outVar == null) {
					m_UnconstraintOut.add(bv);
				}
				if (m_FreeVars.contains(inVar)) {
					m_ConstraintIn.add(bv);
				} else {
					if (inVar == outVar) {
						// do nothing. special case where inVar==outVar holds.
					} else {
						m_UnconstraintIn.add(bv);
					}
				}
			}
			
			for (BoogieVar bv : m_TransFormula.getOutVars().keySet()) {
				TermVariable inVar = m_TransFormula.getInVars().get(bv);
				TermVariable outVar = m_TransFormula.getOutVars().get(bv);
				if (inVar == null) {
					m_UnconstraintIn.add(bv);
				}
				if (m_FreeVars.contains(outVar)) {
					m_ConstraintOut.add(bv);
				} else {
					if (inVar == outVar) {
						// do nothing. special case where inVar==outVar holds.
					} else {
						m_UnconstraintOut.add(bv);
					}
				}
			}

		}

		@Override
		public String toString() {
			return "ConstraintAnalysis [m_ConstraintIn=" + m_ConstraintIn
					+ ", m_UnconstraintIn=" + m_UnconstraintIn
					+ ", m_ConstraintOut=" + m_ConstraintOut
					+ ", m_UnconstraintOut=" + m_UnconstraintOut + "]";
		}

		

	}
	
	private static class NestedConstraintAnalysis extends ModifiableNestedFormulas<ConstraintAnalysis, IPredicate> {

		public NestedConstraintAnalysis(NestedWord<CodeBlock> nestedWord,
				SortedMap<Integer, IPredicate> pendingContexts, 
				NestedFormulas<TransFormula, IPredicate> traceWithFormulas) {
			super(nestedWord, pendingContexts);
			for (int i=0; i<nestedWord.length(); i++) {
				if (getTrace().isCallPosition(i)) {
					TransFormula globalVarAssignment = traceWithFormulas.getGlobalVarAssignment(i);
					setGlobalVarAssignmentAtPos(i, new ConstraintAnalysis(globalVarAssignment)); 
					TransFormula oldVarAssignment = traceWithFormulas.getOldVarAssignment(i);
					setOldVarAssignmentAtPos(i, new ConstraintAnalysis(oldVarAssignment));
					TransFormula localVarAssignment = traceWithFormulas.getLocalVarAssignment(i);
					setLocalVarAssignmentAtPos(i, new ConstraintAnalysis(localVarAssignment));
				} else {
					TransFormula tf = traceWithFormulas.getFormulaFromNonCallPos(i);
					setFormulaAtNonCallPos(i, new ConstraintAnalysis(tf));
				}
			}
			
		}
	}

	
	
//	
//	/**
//	 * Return true if this TransFormula modifies the BoogieVar bv, but after
//	 * executing the TransFormula every value of bv is possible. This is the 
//	 * case for a variable x and the TransFormula of the statement havoc x.
//	 */
//	private boolean isHavoced(BoogieVar bv, TransFormula tf) {
//		TermVariable outVar = tf.getOutVars().get(bv);
//		if (outVar == null) {
//			return false;
//		} else {
//			return !Arrays.asList(tf.getFormula().getFreeVars()).contains(tf.getOutVars().get(bv)); 
//		}
//	}

}
