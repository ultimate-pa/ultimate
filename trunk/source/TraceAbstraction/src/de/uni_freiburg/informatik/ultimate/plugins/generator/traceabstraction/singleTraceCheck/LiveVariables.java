package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * TODO: documentation
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class LiveVariables {
	private Collection<Term>[] m_ConstantsForEachPosition;
	private Set<Term>[] m_LiveConstants;
	private Set<Term>[] m_ForwardLiveConstants;
	private Set<Term>[] m_BackwardLiveConstants;
	//m_LiveVariables[i] are the live variables _before_ statements i
	private Set<BoogieVar>[] m_LiveVariables;
	private Map<Term,BoogieVar> m_Constants2BoogieVar;
	private ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>> m_TraceWithConstants;
	private Map<BoogieVar, TreeMap<Integer, Term>> m_IndexedVarRepresentative;
	private SmtManager m_SmtManager;
	private ModifiableGlobalVariableManager m_modifiableGlobals;
	
	public LiveVariables(ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>> traceWithConstants,
			Map<Term,BoogieVar> constants2BoogieVar,
			Map<BoogieVar, TreeMap<Integer, Term>> indexedVarRepresentative,
			SmtManager smtManager, ModifiableGlobalVariableManager modifiedGlobals) {
		// Initialize members
		m_Constants2BoogieVar = constants2BoogieVar;
		m_TraceWithConstants = traceWithConstants;
		m_IndexedVarRepresentative = indexedVarRepresentative;
		m_SmtManager = smtManager;
		// We don't need the constants for the post-condition, because we do not compute
		// live variables for the post-condition
		m_ConstantsForEachPosition = new Collection[traceWithConstants.getTrace().length() + 2];
		m_ForwardLiveConstants = new Set[m_ConstantsForEachPosition.length + 1];
		m_BackwardLiveConstants = new Set[m_ForwardLiveConstants.length];
		m_LiveConstants = new Set[m_ForwardLiveConstants.length];
		m_LiveVariables = new Set[m_ForwardLiveConstants.length];
		m_modifiableGlobals = modifiedGlobals;
		
		computeLiveVariables();
	}
	
	/**
	 * TODO: documentation
	 * TODO: add constants for post-condition, too.
	 */
	private void fetchConstantsForEachPosition() {
		assert m_ConstantsForEachPosition != null;
		// Add constants for the precondition
		Set<Term> constants = new HashSet<Term>();
		constants.addAll(m_TraceWithConstants.getPrecondition().values());
		m_ConstantsForEachPosition[0] = constants;
		// add constants for the post-condition
		constants = new HashSet<Term>();
		constants.addAll(m_TraceWithConstants.getPostcondition().values());
		m_ConstantsForEachPosition[m_TraceWithConstants.getTrace().length() + 1] = constants;
		for (int i = 0; i < m_TraceWithConstants.getTrace().length(); i++) {
			constants = new HashSet<Term>();
			if (m_TraceWithConstants.getTrace().isCallPosition(i)) {
				assert m_ConstantsForEachPosition[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				constants.addAll(m_TraceWithConstants.getLocalVarAssignment(i).values());
				constants.addAll(m_TraceWithConstants.getGlobalVarAssignment(i).values());
				constants.addAll(m_TraceWithConstants.getOldVarAssignment(i).values());
			} else if (m_TraceWithConstants.getTrace().isReturnPosition(i)) {
				assert m_ConstantsForEachPosition[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				constants.addAll(m_TraceWithConstants.getFormulaFromNonCallPos(i).values());
				int call_pos = m_TraceWithConstants.getTrace().getCallPosition(i);
				constants.addAll(m_TraceWithConstants.getLocalVarAssignment(call_pos).values());
				// Following two lines were added by Matthias to be sure that 
				// we do not miss a variable. Maybe not necessary.
				constants.addAll(m_TraceWithConstants.getGlobalVarAssignment(call_pos).values());
				constants.addAll(m_TraceWithConstants.getOldVarAssignment(call_pos).values());
			} else {
				assert m_ConstantsForEachPosition[i+1] == null : "constants for position " +(i+1)+ " already fetched!";
				constants.addAll(m_TraceWithConstants.getFormulaFromNonCallPos(i).values());
			}
			m_ConstantsForEachPosition[i+1] = constants;
		}
	}

	private void computeLiveVariables() {
		fetchConstantsForEachPosition();
		computeLiveConstants();
		generateLiveVariablesFromLiveConstants();
	}
	
	private void computeLiveConstants() {
		assert m_LiveConstants != null;
		m_LiveConstants[m_LiveConstants.length - 1] = new HashSet<Term>();
		for (int i = m_ConstantsForEachPosition.length - 1; i >= 0; i--) {
			Set<Term> liveConstants = new HashSet<Term>();
			Set<Term> liveConstantsTemp = new HashSet<Term>();
			liveConstantsTemp.addAll(m_ConstantsForEachPosition[i]);
			liveConstantsTemp.addAll(m_LiveConstants[i+1]);
			for (Term t : liveConstantsTemp) {
				BoogieVar bv = m_Constants2BoogieVar.get(t);
				if (bv == null) {
					// do nothing, t is only the corresponding constant of an 
					// auxiliary variable
				} else {
					Map<Integer, Term> indexedVar = m_IndexedVarRepresentative.get(bv);
					if (indexedVar.containsKey(i)) {
						if (!t.equals(indexedVar.get(i))) {
							liveConstants.add(t);
						}
					} else {
						liveConstants.add(t);
					}
				}
			}
			m_LiveConstants[i] = liveConstants;  
		}
	}
	
	private void generateLiveVariablesFromLiveConstants() {
		assert m_LiveVariables != null;
		m_LiveVariables[0] = new HashSet<BoogieVar>(); 
		{
			for (Term t : m_LiveConstants[0]) {
				BoogieVar bv = m_Constants2BoogieVar.get(t);
				if (bv.isGlobal()) {
					m_LiveVariables[0].add(bv);
					if (bv.isOldvar()) {
						m_LiveVariables[0].add(m_SmtManager.getNonOldVar(bv));
					} else {
						m_LiveVariables[0].add(m_SmtManager.getOldVar(bv));
					}
				} else {
					m_LiveVariables[0].add(bv);
				}
			}
		}
		for (int i = 1; i < m_LiveConstants.length; i++) {
			Set<BoogieVar> liveVars = new HashSet<BoogieVar>();
			for (Term t : m_LiveConstants[i]) {
				BoogieVar bv = m_Constants2BoogieVar.get(t);
				if (bv.isGlobal()) {
					liveVars.add(bv);
					if (bv.isOldvar()) {
						liveVars.add(m_SmtManager.getNonOldVar(bv));
					} else {
						liveVars.add(m_SmtManager.getOldVar(bv));
					}
				} else {
					CodeBlock cb = m_TraceWithConstants.getTrace().getSymbolAt(i-1);
					if (cb.getSucceedingProcedure().equals(bv.getProcedure())) {
						liveVars.add(bv);
					}
				}
			}
			m_LiveVariables[i] = liveVars;
		}
		for (int i = 1; i < m_LiveConstants.length-1; i++) {
			if (m_TraceWithConstants.getTrace().isCallPosition(i-1)) {
				if(!m_TraceWithConstants.getTrace().isPendingCall(i-1)) {
					addNonModifiableGlobalsAlongCalledProcedure(m_LiveVariables[i-1], i-1);
				}
			}
		}
	}
	
	
	
	/**
	 * Relevant variables directly before the call that are global are also 
	 * relevant during the whole procedure. Variables that are modifiable by the
	 * procedure (and corresponding oldvars) have already been added (we have
	 * to add the others.  
	 */
	private void addNonModifiableGlobalsAlongCalledProcedure(
			Set<BoogieVar> relevantVariablesBeforeCall, int i) {
		assert m_TraceWithConstants.getTrace().isCallPosition(i);
		assert !m_TraceWithConstants.getTrace().isPendingCall(i);
		Call call = (Call) m_TraceWithConstants.getTrace().getSymbol(i);
		String proc = call.getCallStatement().getMethodName();
		Set<BoogieVar> modifiableGlobals = 
				m_modifiableGlobals.getGlobalVarsAssignment(proc).getOutVars().keySet();
		Set<BoogieVar> oldVarsOfModifiableGlobals = 
				m_modifiableGlobals.getOldVarsAssignment(proc).getOutVars().keySet();
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
			int returnPosition = m_TraceWithConstants.getTrace().getReturnPosition(i);
			for (int pos = i+1; pos<=returnPosition; pos++) {
				assert m_LiveVariables[pos-1].containsAll(varsThatWeHaveToAdd);
				m_LiveVariables[pos].addAll(varsThatWeHaveToAdd);
			}
		}
	}
	
	

	
	/**
	 * Compute the forward live constants (FLC) in the following way:
	 * <li> FLC[0] = empty set
	 * <li> if statement[i] is InternalStatement
	 * <ul> <li> FLC[i] = constantsAtPosition[i] union FLC[i-1] </ul>
	 * <li> if statement[i] is a pending CallStatement
	 * <ul> <li> FLC[i] = constantsAtPosition[i] union GlobalVars(FLC[i-1]) </ul>
	 * <li> if statement[i] is ReturnStatement
	 * <ul> <li> FLC[i] = constantsAtPosition[i] union FLC[correspondingCallPosition]
	 */
	@Deprecated
	private void computeForwardLiveConstants() {
		assert m_ForwardLiveConstants != null;
		assert m_ConstantsForEachPosition != null;
		m_ForwardLiveConstants[0] = new HashSet<Term>();
		for (int i = 0; i < m_ConstantsForEachPosition.length; i++) {
			Set<Term> flc = new HashSet<Term>();
			flc.addAll(m_ConstantsForEachPosition[i]);
			if (i >= 1 && i <= m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isReturnPosition(i-1)) {
				int call_pos = m_TraceWithConstants.getTrace().getCallPosition(i-1);
				if (call_pos >= 0 && (call_pos+1) < m_ForwardLiveConstants.length) {
					flc.addAll(m_ForwardLiveConstants[call_pos+1]);
				}
			} else if (i >= 1 && i <= m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isInternalPosition(i-1)) {
				assert m_ForwardLiveConstants[i] != null;
				flc.addAll(m_ForwardLiveConstants[i]);
			} else if (i >= 1 && i <= m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isPendingCall(i-1)) {
				for (Term t : m_ForwardLiveConstants[i]) {
					BoogieVar bv = m_Constants2BoogieVar.get(t);
					if (bv.isGlobal() || bv.isOldvar()) {
						flc.add(t);
					}
				}
			} else if (i < 1) {
				flc.addAll(m_ForwardLiveConstants[i]);
			}
			m_ForwardLiveConstants[i+1] = flc;
		}
	}
	
	/**
	 * Compute backward live constants (BLC) in the following way:
	 * <li> BLC[n] = empty set, where n is the length of the trace
	 * <li> if statement[i] is InternalStatement 
	 * <ul> <li> FLC[i] = constantsAtPosition[i] union BLC[i+1] </ul>
	 * <li> if statement[i] is a pending CallStatement
	 * <ul> <li> BLC[i] = constantsAtPosition[i] union GlobalVars(BLC[i+1]) </ul>
	 * <li> if statement[i] is a non-pending CallStatement
	 * <ul> <li> BLC[i] = constantsAtPosition[i] union BLC[correspondingReturnPosition] </ul>
	 */
	@Deprecated
	private void computeBackwardLiveConstants() {
		assert m_BackwardLiveConstants != null;
		m_BackwardLiveConstants[m_BackwardLiveConstants.length - 1] = 
				new HashSet<Term>();
		for (int i = m_ConstantsForEachPosition.length - 1; i >= 0; i--) {
			Set<Term> blc = new HashSet<Term>();
			blc.addAll(m_ConstantsForEachPosition[i]);
			if ((i-1) >= 0 && (i-1) < m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isPendingCall(i-1)) {
				for (Term t : m_BackwardLiveConstants[i+1]) {
					BoogieVar bv = m_Constants2BoogieVar.get(t);
					if (bv.isGlobal() || bv.isOldvar()) {
						blc.add(t);
					}
				}
			} else if ((i-1) >= 0 && (i-1) < m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isCallPosition(i-1)) {
				int ret_pos = m_TraceWithConstants.getTrace().getReturnPosition(i-1);
				if ((ret_pos+1) > 0 && (ret_pos+1) < m_TraceWithConstants.getTrace().length()) {
					blc.addAll(m_BackwardLiveConstants[ret_pos]);
				}
			} else if ((i-1) >= 0 && (i-1) < m_TraceWithConstants.getTrace().length() && m_TraceWithConstants.getTrace().isInternalPosition(i-1)) {
				assert m_BackwardLiveConstants[i+1] != null;
				blc.addAll(m_BackwardLiveConstants[i+1]);
			}  else if (i == 0) {
				assert m_BackwardLiveConstants[i+1] != null;
				blc.addAll(m_BackwardLiveConstants[i+1]);
			}
			m_BackwardLiveConstants[i] = blc;
		}
		
	}




	
	private boolean assertLiveVariablesHasBeenComputed() {
		for (int i = 0; i < m_ConstantsForEachPosition.length; i++) {
			assert m_LiveVariables[i] != null : "LiveVariables at position " + i + " has not been computed!";
		}
		return true;
	}
	
	public Set<BoogieVar>[] getLiveVariables() {
		assert m_LiveVariables != null;
		assert assertLiveVariablesHasBeenComputed();
		return m_LiveVariables;
	}
	


}
