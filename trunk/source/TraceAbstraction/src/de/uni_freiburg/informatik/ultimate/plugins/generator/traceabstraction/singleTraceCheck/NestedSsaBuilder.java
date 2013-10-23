package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * A trace has single static assignment form (SSA) is each variable is assigned
 * exactly once ( http://en.wikipedia.org/wiki/Static_single_assignment_form).
 * 
 * This class transforms a trace to an SSA representation by renaming variables.
 * 
 * Roughly variable x is renamed to x_j, where j is the position where j is the
 * last position where x obtained a new value.
 *
 * We use the SSA for checking satisfiability with an SMT solver, therefore we
 * represent the indexed variables by constants.
 * Furthermore we replace all auxiliary variables and branch encoders in the
 * TransFormulas by fresh constants.
 * 
 * We rename inVars of a variable x at trace position i+1 according to the 
 * following scheme.
 * <ul>
 * <li> if x is local:
 * we rename the inVar to x_j, where j is the largest position <= i in the same 
 * calling context, where x is assigned. If x was not assigned in this calling 
 * context up to position i, j is the start of the calling context.
 * <li> if x is global and not oldvar:
 * we rename the inVar to x_j, where j is the largest position <=i where x is
 * assigned. If x was not assigned up to position i, j is the start of the
 * lowest calling context (which is -1 if there are no pending returns and
 * numberOfPendingReturns-1 otherwise).
 * <li> if x is global and oldvar:
 * if x is modifiable in the current calling context we rename the inVar to x_j,
 * where j is the start of the current calling context,
 * if x is not modifiable in the current calling context we threat this variable
 * as a non-oldVar 
 * </ul>
 * If x is assigned at position i+1, we rename the outVar to x_{x+1}.
 * If x in not assigned at position i+1, the outVar does not exist or coincides
 * with the inVar and was already renamed above.
 * @author Matthias Heizmann
 *
 */
public class NestedSsaBuilder {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Script m_Script;
	final SmtManager m_SmtManager;


	/**
	 * Map global BoogieVar bv to the constant bv_j that represents bv at the
	 * moment. 
	 */
	final private Map<BoogieVar,Term> currentGlobalVarVersion =
			new HashMap<BoogieVar,Term>();
	/**
	 * Map local or oldVar BoogieVar bv to the constant bv_j that represents bv
	 * at the moment. 
	 */
	protected Map<BoogieVar,Term> currentLocalAndOldVarVersion;
	
	/**
	 * Stores current versions for local or oldVar that are not visible at the
	 * moment.
	 */
	protected final Stack<Map<BoogieVar,Term>> currentVersionStack =
			new Stack<Map<BoogieVar,Term>>();
	

	Integer startOfCallingContext;
	final Stack<Integer> startOfCallingContextStack =new Stack<Integer>();

	
	final Map<BoogieVar,TreeMap<Integer,Term>> m_IndexedVarRepresentative =
			new HashMap<BoogieVar,TreeMap<Integer,Term>>();
	
	public Map<BoogieVar, TreeMap<Integer, Term>> getIndexedVarRepresentative() {
		return m_IndexedVarRepresentative;
	}
	
	protected final Map<Term,BoogieVar> m_Constants2BoogieVar = new HashMap<Term,BoogieVar>();
	

	public Map<Term, BoogieVar> getConstants2BoogieVar() {
		return m_Constants2BoogieVar;
	}

	protected final NestedFormulas<TransFormula, IPredicate> m_Formulas;
	
	protected final ModifiableNestedFormulas<Term, Term> m_Ssa;
	protected final ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>> m_Variable2Constant;
	
	private final ModifiableGlobalVariableManager m_ModGlobVarManager;
	
	public NestedFormulas<Term, Term> getSsa() {
		return m_Ssa;
	}
	
	public ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>> getVariable2Constant() {
		return m_Variable2Constant;
	}
	
	protected String m_currentProcedure;

	/**
	 * maps position of pending context to position of pending return
	 * the positions of pending contexts are -2,-3,-4,...
	 */
	protected final Map<Integer,Integer> m_PendingContext2PendingReturn = 
			new HashMap<Integer,Integer>();
	

	public NestedSsaBuilder(NestedWord<CodeBlock> trace,
							SmtManager smtManager,
							DefaultTransFormulas defaultTransFormulas) {
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_Formulas = defaultTransFormulas;
		m_ModGlobVarManager = defaultTransFormulas.getModifiableGlobalVariableManager();
		m_Ssa = new ModifiableNestedFormulas<Term, Term>(trace, new TreeMap<Integer, Term>());
		m_Variable2Constant = new ModifiableNestedFormulas<Map<TermVariable,Term>, Map<TermVariable,Term>>(trace, new TreeMap<Integer, Map<TermVariable,Term>>());
		buildSSA();
	}
	

	protected void buildSSA() {
		/* Step 1: We rename the formulas in each pending context.
		 * The index starts from (-1 - numberPendingContexts) and ends at -2.
		 * Furthermore we need the oldVarAssignment and the globalVarAssignment
		 * they will link the pending context with the pending return.
		 */
		final Integer[] pendingReturns = m_Formulas.getTrace().getPendingReturns().keySet().toArray(new Integer[0]);
		final int numberPendingContexts = pendingReturns.length;

		startOfCallingContext = -1 - numberPendingContexts;
		currentLocalAndOldVarVersion = new HashMap<BoogieVar,Term>();

		for (int i=numberPendingContexts-1; i>=0; i--) {
			final int pendingReturnPosition = pendingReturns[i];
			m_PendingContext2PendingReturn.put(startOfCallingContext, pendingReturnPosition);
			Return ret = (Return) m_Formulas.getTrace().getSymbol(pendingReturnPosition);
			Call correspondingCall = ret.getCorrespondingCall();
			m_currentProcedure = getProcedureBefore(correspondingCall);
			
			reVersionModifiableGlobals();
			if (i== numberPendingContexts-1) {
				reVersionModifiableOldVars();
			} else {
				// have already been reversioned at the last oldVarAssignment
			}
			
			IPredicate pendingContext = m_Formulas.getPendingContext(pendingReturnPosition);
			VariableVersioneer pendingContextVV = new VariableVersioneer(pendingContext);
			pendingContextVV.versionPredicate();
			m_Ssa.setPendingContext(pendingReturnPosition, pendingContextVV.getVersioneeredTerm());
			m_Variable2Constant.setPendingContext(pendingReturnPosition, pendingContextVV.getSubstitutionMapping());
			
			TransFormula localVarAssignment = correspondingCall.getTransitionFormula();
			VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
			initLocalVarsVV.versionInVars();

			String calledProcedure = correspondingCall.getCallStatement().getMethodName();
			TransFormula oldVarAssignment = m_Formulas.getOldVarAssignment(pendingReturnPosition);
			VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
			initOldVarsVV.versionInVars();

			startOfCallingContextStack.push(startOfCallingContext);
			startOfCallingContext++;
			m_currentProcedure = calledProcedure;
			currentVersionStack.push(currentLocalAndOldVarVersion);
			currentLocalAndOldVarVersion = new HashMap<BoogieVar,Term>();

			/*
			 * Parameters and oldVars of procedure form that the pending
			 * return returns get the index of the next pending context.
			 */
			initOldVarsVV.versionAssignedVars(startOfCallingContext);
			initLocalVarsVV.versionAssignedVars(startOfCallingContext);

			m_Ssa.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
			m_Variable2Constant.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getSubstitutionMapping());
			m_Ssa.setLocalVarAssignmentAtPos(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
			m_Variable2Constant.setLocalVarAssignmentAtPos(pendingReturnPosition, initLocalVarsVV.getSubstitutionMapping());
		}
				
		assert (startOfCallingContext == -1);

		/*
		 * Step 2: We rename the formula of the precondition.
		 * We use as index -1.
		 * 
		 */
		if (m_currentProcedure == null) {
			assert numberPendingContexts == 0;
			CodeBlock firstCodeBlock = m_Formulas.getTrace().getSymbolAt(0);
			m_currentProcedure = getProcedureBefore(firstCodeBlock);
		}
		reVersionModifiableGlobals();
		if (pendingReturns.length == 0) {
			reVersionModifiableOldVars();
		} else {
			// have already been reversioned at the last oldVarAssignment
		}
		VariableVersioneer precondVV = new VariableVersioneer(m_Formulas.getPrecondition());
		precondVV.versionPredicate();
		m_Ssa.setPrecondition(precondVV.getVersioneeredTerm());
		m_Variable2Constant.setPrecondition(precondVV.getSubstitutionMapping());
		
		
		/*
		 * Step 3: We rename the TransFormulas of the traces CodeBlocks
		 */
		int numberOfPendingCalls = 0;
		for (int i=0; i < m_Formulas.getTrace().length(); i++) {
			CodeBlock symbol = m_Formulas.getTrace().getSymbolAt(i);
			assert (!(symbol instanceof GotoEdge)) : "TraceChecker does not support GotoEdges";
			
			TransFormula tf;
			if (m_Formulas.getTrace().isCallPosition(i)) {
				tf = m_Formulas.getLocalVarAssignment(i);
			} else {
				tf = m_Formulas.getFormulaFromNonCallPos(i);
			}
			
			VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();
			
			if (m_Formulas.getTrace().isCallPosition(i)) {
				assert (symbol instanceof Call) : 
					"current implementation supports only Call";
				if (m_Formulas.getTrace().isPendingCall(i)) {
					numberOfPendingCalls++;
				}
				Call call = (Call) symbol;
				String calledProcedure = call.getCallStatement().getMethodName();
				m_currentProcedure = calledProcedure;
				TransFormula oldVarAssignment = m_Formulas.getOldVarAssignment(i);
				VariableVersioneer initOldVarsVV = 
											new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				startOfCallingContextStack.push(startOfCallingContext);
				startOfCallingContext = i;
				initOldVarsVV.versionAssignedVars(i);
				m_Ssa.setOldVarAssignmentAtPos(i, initOldVarsVV.getVersioneeredTerm());
				m_Variable2Constant.setOldVarAssignmentAtPos(i, initOldVarsVV.getSubstitutionMapping());

				TransFormula globalVarAssignment = m_Formulas.getGlobalVarAssignment(i);
				VariableVersioneer initGlobalVarsVV = 
						new VariableVersioneer(globalVarAssignment);
				initGlobalVarsVV.versionInVars();
				initGlobalVarsVV.versionAssignedVars(i);
				m_Ssa.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getVersioneeredTerm());
				m_Variable2Constant.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getSubstitutionMapping());
				currentVersionStack.push(currentLocalAndOldVarVersion);
				currentLocalAndOldVarVersion = new HashMap<BoogieVar,Term>();
			}
			if (m_Formulas.getTrace().isReturnPosition(i)) {
				Return ret = (Return) symbol;
				m_currentProcedure = ret.getCallerProgramPoint().getProcedure();
				currentLocalAndOldVarVersion = currentVersionStack.pop();
				startOfCallingContext = startOfCallingContextStack.pop();
			}
			tfVV.versionAssignedVars(i);
			tfVV.versionBranchEncoders(i);
			tfVV.replaceAuxVars();
			if (m_Formulas.getTrace().isCallPosition(i)) {
				m_Ssa.setLocalVarAssignmentAtPos(i, tfVV.getVersioneeredTerm());
				m_Variable2Constant.setLocalVarAssignmentAtPos(i, tfVV.getSubstitutionMapping());
			}
			else {
				m_Ssa.setFormulaAtNonCallPos(i, tfVV.getVersioneeredTerm());
				m_Variable2Constant.setFormulaAtNonCallPos(i, tfVV.getSubstitutionMapping());
			}
		}
		
		/* Step 4: We rename the postcondition.
		 */
		assert currentVersionStack.size() == numberOfPendingCalls;
		assert numberOfPendingCalls > 0 || startOfCallingContext == -1 - numberPendingContexts;
		assert numberOfPendingCalls == 0 || numberPendingContexts == 0;

		VariableVersioneer postCondVV = new VariableVersioneer(m_Formulas.getPostcondition());
		postCondVV.versionPredicate();
		m_Ssa.setPostcondition(postCondVV.getVersioneeredTerm());
		m_Variable2Constant.setPostcondition(postCondVV.getSubstitutionMapping());
		
		


	}


	/**
	 * Set new var version for all globals that are modifiable by the current
	 * procedure.
	 */
	protected void reVersionModifiableGlobals() {
		Set<BoogieVar> modifiable = m_ModGlobVarManager.getGlobalVarsAssignment(
				m_currentProcedure).getAssignedVars();
		for (BoogieVar bv : modifiable) {
			setCurrentVarVersion(bv, startOfCallingContext);
		}
	}
	
	
	/**
	 * Set new var version for all oldVars that are modifiable by the current
	 * procedure.
	 */
	protected void reVersionModifiableOldVars() {
		Set<BoogieVar> modifiable = m_ModGlobVarManager.getOldVarsAssignment(
				m_currentProcedure).getAssignedVars();
		for (BoogieVar bv : modifiable) {
			setCurrentVarVersion(bv, startOfCallingContext);
		}
	}
	
	
	/**
	 * Returns the procedure in which a system is before executing the 
	 * CodeBlock cb.
	 * If cb is a call, the result is the name of the caller, if cb is a return
	 * the result is the callee (from that we return.
	 */
	public String getProcedureBefore(CodeBlock cb) {
		ProgramPoint pp = (ProgramPoint) cb.getSource();
		return pp.getProcedure();
	}
	

	/**
	 * Compute identifier of the Constant that represents the branch encoder tv
	 * at position pos.
	 */
	public static String branchEncoderConstantName(TermVariable tv, int pos) {
		String name = tv.getName() + "_" + pos;
		return name;
	}
	
	

	class VariableVersioneer {
		private final TransFormula m_TF;
		private final IPredicate m_Pred;
		private final Map<TermVariable, Term> m_SubstitutionMapping = 
				new HashMap<TermVariable, Term>();
		private Term m_formula;
		
		public VariableVersioneer(TransFormula tf) {
			m_TF = tf;
			m_Pred = null;
			m_formula = tf.getFormula();
		}
		
		public VariableVersioneer(IPredicate pred) {
			m_TF = null;
			m_Pred = pred;
			m_formula = pred.getFormula();
		}

		public void versionInVars() {
			for (BoogieVar bv : m_TF.getInVars().keySet()) {
				TermVariable tv = m_TF.getInVars().get(bv);
				Term versioneered = getCurrentVarVersion(bv);
				m_Constants2BoogieVar.put(versioneered, bv);
				m_SubstitutionMapping.put(tv, versioneered);
			}
		}

		public void versionAssignedVars(int currentPos) {
			for (BoogieVar bv : m_TF.getAssignedVars()) {
				TermVariable tv = m_TF.getOutVars().get(bv);
				Term versioneered = setCurrentVarVersion(bv,currentPos);
				m_Constants2BoogieVar.put(versioneered, bv);
				m_SubstitutionMapping.put(tv, versioneered);
			}
		}
		
		public void versionBranchEncoders(int currentPos) {
			for (TermVariable tv : m_TF.getBranchEncoders()) {
				String name = branchEncoderConstantName(tv, currentPos);
				m_Script.declareFun(name, new Sort[0], tv.getSort());
				m_SubstitutionMapping.put(tv, m_Script.term(name));
			}
		}
		
		public void replaceAuxVars() {
			for (TermVariable tv : m_TF.getAuxVars()) {
				Term freshConst = m_SmtManager.getFreshConstant(tv);
				m_SubstitutionMapping.put(tv, freshConst);
			}
		}
		
		public void versionPredicate() {
			for (BoogieVar bv : m_Pred.getVars()) {
				TermVariable tv = bv.getTermVariable();
				Term versioneered = getCurrentVarVersion(bv);
				m_Constants2BoogieVar.put(versioneered, bv);
				m_SubstitutionMapping.put(tv, versioneered);
			}
		}
		
		public Term getVersioneeredTerm() {
			Substitution subst = new Substitution(m_SubstitutionMapping, m_Script);
			Term result = subst.transform(m_formula);
			assert result.getFreeVars().length == 0 : 
				"free vars in versioneered term";
			return result;
		}

		public Map<TermVariable, Term> getSubstitutionMapping() {
			return m_SubstitutionMapping;
		}
		
	}
		
		
		/**
		 * Get the current version of BoogieVariable bv. Construct this version
		 * if it does not exist yet.
		 */
		private Term getCurrentVarVersion(BoogieVar bv) {
			Term result;
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					result = currentLocalAndOldVarVersion.get(bv);
					if (result == null) {
						throw new UnsupportedOperationException(
								"not yet implemented: old var of non-modifialbe");
					}
				} else {
					result = currentGlobalVarVersion.get(bv);
					if (result == null) {
						// variable was not yet assigned in trace
						// FIXME: in oder to be compliant with the documentation
						// we should use an initial calling context
						// -1-numberOfCallingContexts. But this should not have
						// an impact on correctness.
						result = setCurrentVarVersion(bv, -1);
					}
				}
			} else {
				result = currentLocalAndOldVarVersion.get(bv);
				if (result == null) {
					// variable was not yet assigned in the calling context
					result = setCurrentVarVersion(bv, startOfCallingContext);
				}
			}
			return result;
		}
		


		/**
		 * Set the current version of BoogieVariable bv to the constant b_index
		 * and return b_index.
		 */
		private Term setCurrentVarVersion(BoogieVar bv, int index) {
			Term var = buildVersion(bv, index);
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					assert (index == startOfCallingContext) :
						"oldVars may only be assigned at entry of procedure";
					currentLocalAndOldVarVersion.put(bv, var);
				} else {
					currentGlobalVarVersion.put(bv, var);
				}
			}
			else {
				currentLocalAndOldVarVersion.put(bv, var);
			}
			return var; 
		}
		
		
		
		/**
		 * Build constant bv_index that represents BoogieVar bv that obtains
		 * a new value at position index.
		 */
		private Term buildVersion(BoogieVar bv, int index) {
			TreeMap<Integer, Term> index2constant = m_IndexedVarRepresentative.get(bv);
			if (index2constant == null) {
				index2constant = new TreeMap<Integer, Term>();
				m_IndexedVarRepresentative.put(bv,index2constant);
			}
			assert !index2constant.containsKey(index) : "version was already constructed";
			Term constant = m_SmtManager.getIndexedConstant(bv, index);
			index2constant.put(index, constant);
			return constant;
		}
		
		
		
		/**
		 * May the corresponding global var of the oldvar bv be modified in
		 * in the current calling context (according to modifies clauses?) 
		 */
		private boolean modifiedInCurrentCallingContext(BoogieVar bv) {
			if (!bv.isGlobal()) {
				throw new IllegalArgumentException(bv + " no global var");
			}
			TransFormula oldVarAssignment;
			if (startOfCallingContext >= 0) {
				oldVarAssignment = m_Formulas.getOldVarAssignment(startOfCallingContext);
			} else if (startOfCallingContext == -1) {
				// from some point of view each variable is modified in the 
				// initial calling context, because variables get their
				// initial values here
				return true;
			} else {
				assert startOfCallingContext < -1;
				int pendingReturnPosition = m_PendingContext2PendingReturn.get(startOfCallingContext);
				oldVarAssignment = m_Formulas.getOldVarAssignment(pendingReturnPosition);
			}
			boolean isModified;
			if (bv.isOldvar()) {
				isModified = oldVarAssignment.getAssignedVars().contains(bv);
			} else {
				isModified = oldVarAssignment.getInVars().keySet().contains(bv);
			}
			return isModified;
		}
}
