package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

/**
 * Compute the live variables along a trace. Use data structures from the SSA
 * construction for this computation.
 * Position i in the list of live variables refers to the position between
 * CodeBlock i-1 and CodeBlock i in the trace. Position 0 in the list of live
 * variables refers to the precondition, Position trace.length+1 refers to the
 * postcondition.
 * A variable is live at position i if it is used in a CodeBlock with 
 * position <i and it is used in a CodeBlock with position >= i and if it
 * belongs to the current calling context.
 * We have the following definition of used:
 * A variable is used in a CodeBlock, if it occurs in the code block.
 * If g is a global variable that is modified by procedure proc, the 
 * the variables g and old(g) are used in each call to proc and in each return
 * from proc.
 * Furthermore each global variable (even if not modified) that occur in a 
 * procedure (along this trace) is used at the return of this procedure.
 * @author musab@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 *
 */
public class LiveVariables {
	private final Map<Term,BoogieVar> m_Constants2BoogieVar;
	private final ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>> m_TraceWithConstants;
	private final Map<BoogieVar, TreeMap<Integer, Term>> m_IndexedVarRepresentative;

	
	private final Collection<Term>[] m_ConstantsForEachPosition;
	private final Set<Term>[] m_LiveConstants;
	//m_LiveVariables[i] are the live variables _before_ statement i
	private final Set<BoogieVar>[] m_LiveVariables;

	
	
	public LiveVariables(ModifiableNestedFormulas<Map<TermVariable,Term>, 
			Map<TermVariable,Term>> traceWithConstants,
			Map<Term,BoogieVar> constants2BoogieVar,
			Map<BoogieVar, TreeMap<Integer, Term>> indexedVarRepresentative,
			SmtManager smtManager, ModifiableGlobalVariableManager modifiedGlobals) {
		m_Constants2BoogieVar = constants2BoogieVar;
		m_TraceWithConstants = traceWithConstants;
		m_IndexedVarRepresentative = indexedVarRepresentative;
		// We compute constants for each position of trace, the precondition
		// and the postcondition.
		m_ConstantsForEachPosition = fetchConstantsForEachPosition();
		m_LiveConstants = computeLiveConstants();
		m_LiveVariables = computeLiveVariables();
	}
	
	/**
	 * Fetch all constants (which are indexed instances of a variable in the 
	 * SSA) that represent BoogieVars for the precondition, for each CodeBlock
	 * of the trace and for the post-condition.
	 * Returns an array of length (trace.length + 2) such that
 	 * <ul>
	 * <li> at pos = 0, there are the constants of the precondition
	 * <li> at pos = trace.length + 1, there are the constants of the 
	 * postcondition
	 * <li> at pos = i+1 there are the constants for the CodeBlocks of the 
	 * trace at position i.
	 * </ul>
	 * The assignment of TransFormulas to positions is the same as for the
	 * computation of nested interpolants:
	 * <ul>
	 * <li> if i is an internal position we use the formula from this position
	 * <li> if i is the position of a pending call, we use the 
	 * localVarAssignment, the globalVarAssignment and the OldVarAssignment,
	 * <li> if i is the position of a non-pending call, we use the 
	 * globalVarAssignment
	 * <li> if i is a return position, we use the formula of the
	 * return position, the localVarAssignment and the oldVarAssignment
	 * </ul>
	 * 
	 */
	private Collection<Term>[] fetchConstantsForEachPosition() {
		@SuppressWarnings("unchecked")
		Collection<Term>[] result = new Collection[m_TraceWithConstants.getTrace().length() + 2];
		// Add constants for the precondition
		result[0] = extractVarConstants(
				m_TraceWithConstants.getPrecondition().values());
		// add constants for the post-condition
		int lastPosition = m_TraceWithConstants.getTrace().length() + 1;
		result[lastPosition] = extractVarConstants(
				m_TraceWithConstants.getPostcondition().values());
		for (int i = 0; i < m_TraceWithConstants.getTrace().length(); i++) {
			if (m_TraceWithConstants.getTrace().isCallPosition(i)) {
				assert result[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				if (m_TraceWithConstants.getTrace().isPendingCall(i)) {
					result[i+1] = extractVarConstants(
							m_TraceWithConstants.getLocalVarAssignment(i).values(),
							m_TraceWithConstants.getGlobalVarAssignment(i).values(),
							m_TraceWithConstants.getOldVarAssignment(i).values());
				} else {
					result[i+1] = extractVarConstants(
							m_TraceWithConstants.getGlobalVarAssignment(i).values());
				}
			} else if (m_TraceWithConstants.getTrace().isReturnPosition(i)) {
				assert result[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				if (m_TraceWithConstants.getTrace().isPendingReturn(i)) {
					throw new AssertionError("not yet implemented");
				} else {
					int call_pos = m_TraceWithConstants.getTrace().getCallPosition(i);
					result[i+1] = extractVarConstants(
							m_TraceWithConstants.getFormulaFromNonCallPos(i).values(),
							m_TraceWithConstants.getLocalVarAssignment(call_pos).values(),
							m_TraceWithConstants.getOldVarAssignment(call_pos).values());
				}
			} else {
				assert result[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				assert m_TraceWithConstants.getTrace().isInternalPosition(i);
				result[i+1] = extractVarConstants(
						m_TraceWithConstants.getFormulaFromNonCallPos(i).values());
			}
		}
		return result;
	}

	/**
	 * Returns a set that contains all terms from collections that represent 
	 * a BoogieVar. (used to filter out constants that only correspond to
	 * auxVars)
	 */
	@SafeVarargs
	private final Set<Term> extractVarConstants(Collection<Term>... collections) {
		Set<Term> result = new HashSet<Term>();
		for (Collection<Term> terms : collections) {
			for (Term term : terms) {
				if (m_Constants2BoogieVar.containsKey(term)) {
					// constant represents a BoogieVar
					result.add(term);
				}
			}
		}
		return result;
	}


	/**
	 * Compute at which position of the trace which constant is live.
	 * Returns an array of length (trace.length + 1) where the position i refers
	 * to the position between CodeBlock i-1 and CodeBlock i. Furthermore
	 * position 0 refers to the precondition and position trace.length + 1 
	 * refers to the postcondition.
	 * A constant is live at position i if it is used in a CodeBlock with 
	 * position <i and it is used in a CodeBlock with position >= i and if it
	 * belongs to the current calling context.
	 */
	private Set<Term>[] computeLiveConstants() {
		// Idea of this algorithm:
		// - traverse the trace backwards
		// - add all constants that occur
		// - remove all constants that have the index of the current position
		//   (because they occur here for the first time and are not contained
		//   in a prefix of the trace)
		// - take care for contexts, calls returns
		@SuppressWarnings("unchecked")
		Set<Term>[] result = new Set[m_TraceWithConstants.getTrace().length() + 1];
		{
			HashSet<Term> liveConstants = new HashSet<Term>(m_ConstantsForEachPosition[result.length - 1]);
			removeConstantsWithIndex_i(liveConstants, result.length - 1);
			result[result.length - 1] = liveConstants;
		}
		for (int i = result.length - 2; i >= 0; i--) {
			HashSet<Term> liveConstants = new HashSet<Term>();
			if (m_TraceWithConstants.getTrace().isCallPosition(i)) {
				String caller = m_TraceWithConstants.getTrace().getSymbol(i).getPreceedingProcedure();
				if (m_TraceWithConstants.getTrace().isPendingCall(i)) {
					addGlobals(liveConstants, result[i+1]);
					addGlobals(liveConstants, m_ConstantsForEachPosition[i+1]);
					addLocals(caller, liveConstants, m_ConstantsForEachPosition[i+1]);
				} else {
					int returnPos = m_TraceWithConstants.getTrace().getReturnPosition(i);
					addLocals(caller, liveConstants, result[returnPos+1]);
					addLocals(caller, liveConstants, m_ConstantsForEachPosition[returnPos+1]);
					removeConstantsWithIndex_i(liveConstants, returnPos);
					addGlobals(liveConstants, result[i+1]);
					addGlobals(liveConstants, m_ConstantsForEachPosition[i+1]);

				}
			} else if (m_TraceWithConstants.getTrace().isReturnPosition(i)) {
				String callee = m_TraceWithConstants.getTrace().getSymbol(i).getPreceedingProcedure();
				addGlobals(liveConstants, result[i+1]);
				addGlobals(liveConstants, m_ConstantsForEachPosition[i+1]);
				addLocals(callee, liveConstants, m_ConstantsForEachPosition[i+1]);
			} else {
				assert m_TraceWithConstants.getTrace().isInternalPosition(i);
				liveConstants.addAll(m_ConstantsForEachPosition[i+1]);
				liveConstants.addAll(result[i+1]);
			}
			removeConstantsWithIndex_i(liveConstants, i);
			result[i] = liveConstants;  
		}
		return result;
	}
	
	/**
	 * Add to writeSet all constants from readCollection that correspond to
	 * global BoogieVars.
	 */
	private void addGlobals(HashSet<Term> writeSet, Collection<Term> readCollection) {
		for (Term term : readCollection) {
			BoogieVar bv = m_Constants2BoogieVar.get(term);
			if (bv.isGlobal()) {
				writeSet.add(term);
			}
		}
	}
	
	/**
	 * Add to writeSet all constants from readCollection that correspond to
	 * local BoogieVars of procedure proc
	 */
	private void addLocals(String proc, HashSet<Term> writeSet, Collection<Term> readCollection) {
		for (Term term : readCollection) {
			BoogieVar bv = m_Constants2BoogieVar.get(term);
			if (!bv.isGlobal()) {
				if (bv.getProcedure().equals(proc)) {
					writeSet.add(term);
				}
			}
		}
	}

	/**
	 * Remove from set all constants whose index is i.
	 */
	private void removeConstantsWithIndex_i(HashSet<Term> set, int i) {
		Iterator<Term> it = set.iterator();
		while (it.hasNext()) {
			Term term = it.next();
			BoogieVar bv = m_Constants2BoogieVar.get(term);
			Map<Integer, Term> indexedVar = m_IndexedVarRepresentative.get(bv);
			if (indexedVar.get(i) == term) {
				it.remove();
			}
		}
	}
	
	
	
	/**
	 * Use the live constants to compute live variables.
	 * The corresponding BoogieVar of each live constant is a live variable.
	 * Furthermore each global variable that occurs between a call and return
	 * is live until the return.
	 */
	private Set<BoogieVar>[] computeLiveVariables() {
		@SuppressWarnings("unchecked")
		Set<BoogieVar>[] result = new Set[m_TraceWithConstants.getTrace().length() + 1];
		ScopedHashSet<BoogieVar> globalVarsBetweenCallAndReturn = 
				new ScopedHashSet<BoogieVar>();
		for (int i = 0; i < result.length; i++) {
			if (i > 0 && i < result.length-1 && 
					m_TraceWithConstants.getTrace().isCallPosition(i-1) && 
					!m_TraceWithConstants.getTrace().isPendingCall(i-1)) {
				globalVarsBetweenCallAndReturn.beginScope();
			}
			if (i > 0 && i < result.length-1 && 
					m_TraceWithConstants.getTrace().isReturnPosition(i-1)) {
				 if (m_TraceWithConstants.getTrace().isPendingReturn(i-1)) {
					 throw new AssertionError("not yet implemented");
				 } else {
					 globalVarsBetweenCallAndReturn.endScope();
				 }
			}
			Set<BoogieVar> liveVars = new HashSet<BoogieVar>();
			for (Term t : m_LiveConstants[i]) {
				BoogieVar bv = m_Constants2BoogieVar.get(t);
				if (!globalVarsBetweenCallAndReturn.isEmptyScope() && bv.isGlobal()) {
					globalVarsBetweenCallAndReturn.add(bv);
				} else {
					liveVars.add(bv);
				}
			}
			liveVars.addAll(globalVarsBetweenCallAndReturn);
			result[i] = liveVars;
		}
		return result;
	}
	
	public Set<BoogieVar>[] getLiveVariables() {
		return m_LiveVariables;
	}
}
