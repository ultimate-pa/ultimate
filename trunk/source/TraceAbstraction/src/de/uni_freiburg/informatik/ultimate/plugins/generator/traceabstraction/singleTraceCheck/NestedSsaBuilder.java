package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
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

	protected final TraceWithFormulas<TransFormula, IPredicate> m_TraceWF;
	
	protected final SsaData m_SsaData;
	
	private final ModifiableGlobalVariableManager m_ModGlobVarManager;
	

	
	protected NestedSsa m_Ssa;
	
	public NestedSsa getSsa() {
		return m_Ssa;
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
		m_TraceWF = defaultTransFormulas;
		m_ModGlobVarManager = defaultTransFormulas.getModifiableGlobalVariableManager();
		m_SsaData = new SsaData();
		buildSSA();
	}
	

	protected void buildSSA() {
		/* Step 1: We rename the formulas in each pending context.
		 * The index starts from (-1 - numberPendingContexts) and ends at -2.
		 * Furthermore we need the oldVarAssignment and the globalVarAssignment
		 * they will link the pending context with the pending return.
		 */
		final int numberPendingContexts = m_TraceWF.getPendingContexts().size();
		final List<Integer> pendingReturns;
		if (numberPendingContexts > 0) {
			pendingReturns = positionsOfPendingReturns(m_TraceWF.getTrace());
		} else {
			pendingReturns = new ArrayList<Integer>(0);
		}
		assert pendingReturns.size() == numberPendingContexts;

		startOfCallingContext = -1 - numberPendingContexts;
		currentLocalAndOldVarVersion = new HashMap<BoogieVar,Term>();

		for (int i=numberPendingContexts-1; i>=0; i--) {
			final int pendingReturnPosition = pendingReturns.get(i);
			m_PendingContext2PendingReturn.put(startOfCallingContext, pendingReturnPosition);
			Return ret = (Return) m_TraceWF.getTrace().getSymbol(pendingReturnPosition);
			Call correspondingCall = ret.getCorrespondingCall();
			m_currentProcedure = getProcedureBefore(correspondingCall);
			
			reVersionModifiableGlobals();
			if (i== numberPendingContexts-1) {
				reVersionModifiableOldVars();
			} else {
				// have already been reversioned at the last oldVarAssignment
			}
			
			IPredicate pendingContext = m_TraceWF.getPendingContexts().get(pendingReturnPosition);
			VariableVersioneer pendingContextVV = new VariableVersioneer(pendingContext);
			pendingContextVV.versionPredicate();
			Term versioneeredContext = pendingContextVV.getVersioneeredTerm();
			m_SsaData.putPendingContext(pendingReturnPosition, versioneeredContext);
			
			TransFormula localVarAssignment = correspondingCall.getTransitionFormula();
			VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
			initLocalVarsVV.versionInVars();

			String calledProcedure = correspondingCall.getCallStatement().getMethodName();
			TransFormula oldVarAssignment = m_TraceWF.getOldVarAssignment(pendingReturnPosition);
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

			m_SsaData.putOldVarAssign(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
			m_SsaData.putLocalVarAssign(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
		}
				
		assert (startOfCallingContext == -1);

		/*
		 * Step 2: We rename the formula of the precondition.
		 * We use as index -1.
		 * 
		 */
		if (m_currentProcedure == null) {
			assert numberPendingContexts == 0;
			CodeBlock firstCodeBlock = m_TraceWF.getTrace().getSymbolAt(0);
			m_currentProcedure = getProcedureBefore(firstCodeBlock);
		}
		reVersionModifiableGlobals();
		if (pendingReturns.isEmpty()) {
			reVersionModifiableOldVars();
		} else {
			// have already been reversioned at the last oldVarAssignment
		}
		VariableVersioneer precondVV = new VariableVersioneer(m_TraceWF.getPrecondition());
		precondVV.versionPredicate();
		Term versioneeredPrecondition = precondVV.getVersioneeredTerm();
		m_SsaData.setPrecondition(versioneeredPrecondition);
		
		
		/*
		 * Step 3: We rename the TransFormulas of the traces CodeBlocks
		 */
		int numberOfPendingCalls = 0;
		for (int i=0; i < m_TraceWF.getTrace().length(); i++) {
			CodeBlock symbol = m_TraceWF.getTrace().getSymbolAt(i);
			assert (!(symbol instanceof GotoEdge)) : "TraceChecker does not support GotoEdges";
			
			TransFormula tf;
			if (m_TraceWF.getTrace().isCallPosition(i)) {
				tf = m_TraceWF.getLocalVarAssignment(i);
			} else {
				tf = m_TraceWF.getFormulaFromNonCallPos(i);
			}
			
			VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();
			
			if (m_TraceWF.getTrace().isCallPosition(i)) {
				assert (symbol instanceof Call) : 
					"current implementation supports only Call";
				if (m_TraceWF.getTrace().isPendingCall(i)) {
					numberOfPendingCalls++;
				}
				Call call = (Call) symbol;
				String calledProcedure = call.getCallStatement().getMethodName();
				m_currentProcedure = calledProcedure;
				TransFormula oldVarAssignment = m_TraceWF.getOldVarAssignment(i);
				VariableVersioneer initOldVarsVV = 
											new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				startOfCallingContextStack.push(startOfCallingContext);
				startOfCallingContext = i;
				initOldVarsVV.versionAssignedVars(i);
				m_SsaData.putOldVarAssign(i, initOldVarsVV.getVersioneeredTerm());

				TransFormula globalVarAssignment = m_TraceWF.getGlobalVarAssignment(i);
				VariableVersioneer initGlobalVarsVV = 
						new VariableVersioneer(globalVarAssignment);
				initGlobalVarsVV.versionInVars();
				initGlobalVarsVV.versionAssignedVars(i);
				m_SsaData.putGlobalVarAssign(i, initGlobalVarsVV.getVersioneeredTerm());
				currentVersionStack.push(currentLocalAndOldVarVersion);
				currentLocalAndOldVarVersion = new HashMap<BoogieVar,Term>();
			}
			if (m_TraceWF.getTrace().isReturnPosition(i)) {
				Return ret = (Return) symbol;
				m_currentProcedure = ret.getCallerProgramPoint().getProcedure();
				currentLocalAndOldVarVersion = currentVersionStack.pop();
				startOfCallingContext = startOfCallingContextStack.pop();
			}
			tfVV.versionAssignedVars(i);
			tfVV.versionBranchEncoders(i);
			tfVV.replaceAuxVars();
			if (m_TraceWF.getTrace().isCallPosition(i)) {
				m_SsaData.putLocalVarAssign(i, tfVV.getVersioneeredTerm());
			}
			else {
				m_SsaData.putNonCallFormula(i, tfVV.getVersioneeredTerm());
			}
		}
		
		/* Step 4: We rename the postcondition.
		 */
		assert currentVersionStack.size() == numberOfPendingCalls;
		assert numberOfPendingCalls > 0 || startOfCallingContext == -1 - numberPendingContexts;
		assert numberOfPendingCalls == 0 || numberPendingContexts == 0;

		VariableVersioneer postCondVV = new VariableVersioneer(m_TraceWF.getPostcondition());
		postCondVV.versionPredicate();
		Term versioneeredPostcondition = postCondVV.getVersioneeredTerm();
		m_SsaData.setPostcondition(versioneeredPostcondition);
		
		

		m_Ssa = new NestedSsa(
		m_TraceWF,
		m_SsaData.getPrecondition(),
		m_SsaData.getPostcondition(),
		m_SsaData.getTerms(),
		m_SsaData.getLocalVarAssignmentAtCall(),
		m_SsaData.getGlobalOldVarAssignmentAtCall(),
		m_SsaData.getPendingContexts(),
		m_Constants2BoogieVar);
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
				oldVarAssignment = m_TraceWF.getOldVarAssignment(startOfCallingContext);
			} else if (startOfCallingContext == -1) {
				// from some point of view each variable is modified in the 
				// initial calling context, because variables get their
				// initial values here
				return true;
			} else {
				assert startOfCallingContext < -1;
				int pendingReturnPosition = m_PendingContext2PendingReturn.get(startOfCallingContext);
				oldVarAssignment = m_TraceWF.getOldVarAssignment(pendingReturnPosition);
			}
			boolean isModified;
			if (bv.isOldvar()) {
				isModified = oldVarAssignment.getAssignedVars().contains(bv);
			} else {
				isModified = oldVarAssignment.getInVars().keySet().contains(bv);
			}
			return isModified;
		}
		

		
		@Deprecated //pendingContexts is now Map
		protected List<Integer> positionsOfPendingReturns(NestedWord<CodeBlock> nw) {
			List<Integer> result = new ArrayList<Integer>();
			for (int i=0; i<nw.length(); i++) {
				if (nw.isPendingReturn(i)) {
					result.add(i);
				}
			}
			return result;
		}
	
		
		/**
		 * Buffer to collect information needed to construt a SSA.
		 */
		class SsaData {
			/**
			 * SSA form of Precondition.
			 * Original precondition where all variables get index -1.  
			 */
			private Term m_Precondition;
			
			/**
			 * SSA form of Postcondition. 
			 * Original postcondition where all variables get as index the last position
			 * of the trace where this variable has been modified (with respect to 
			 * calling context).  
			 */
			private Term m_Postcondition;
			
			/**
			 * If index i is an internal position or a return transition in the
			 * nested trace Term[i] represents the i-th statement.
			 * If index i is a call position Term[i] represents the assignment 
			 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the
			 * global variables modified by the called procedure.  
			 */
			private final Term[] m_Terms;
			
			/**
			 * Maps a call position to a formula that represents the assignment 
			 * {@code x_1,...,x_n := t_1,...,t_n} where x_1,...,x_n are the parameters
			 * of the callee and t_1,...,t_n are the arguments of the caller.
			 */
			private final Map<Integer,Term> m_LocalVarAssignmentAtCall;
			
			/**
			 * Maps a call position to a formula that represents the assignment 
			 * {@code old(g_1),...,old(g_n) := g_1,...,g_n} where g_1,...,g_n are the
			 * global variables modified by the called procedure.  
			 */
			private final Map<Integer,Term> m_GlobalOldVarAssignmentAtCall;
			
			
			/**
			 * Maps a pending return position to a formula which represents the state of
			 * the procedure to which is returned before the return.
			 */
			private final SortedMap<Integer,Term> m_PendingContexts;
			
			public SsaData() {
				m_Terms = new Term[m_TraceWF.getTrace().length()];
				m_LocalVarAssignmentAtCall = new HashMap<Integer,Term>();
				m_GlobalOldVarAssignmentAtCall = new HashMap<Integer,Term>();
				m_PendingContexts = new TreeMap<Integer,Term>();
			}


			public Term getPrecondition() {
				return m_Precondition;
			}


			public void setPrecondition(Term precondition) {
				m_Precondition = precondition;
			}


			public Term getPostcondition() {
				return m_Postcondition;
			}


			public void setPostcondition(Term postcondition) {
				m_Postcondition = postcondition;
			}


			public Term[] getTerms() {
				return m_Terms;
			}


			public Map<Integer, Term> getLocalVarAssignmentAtCall() {
				return m_LocalVarAssignmentAtCall;
			}


			public Map<Integer, Term> getGlobalOldVarAssignmentAtCall() {
				return m_GlobalOldVarAssignmentAtCall;
			}


			public SortedMap<Integer, Term> getPendingContexts() {
				return m_PendingContexts;
			}


			public void putOldVarAssign(Integer pos, Term term) {
				assert m_TraceWF.getTrace().isCallPosition(pos) || m_TraceWF.getTrace().isPendingReturn(pos);
				assert m_GlobalOldVarAssignmentAtCall.get(pos) == null;
				m_GlobalOldVarAssignmentAtCall.put(pos, term);
			}
			
			public void putLocalVarAssign(Integer pos, Term term) {
				assert m_TraceWF.getTrace().isCallPosition(pos) || m_TraceWF.getTrace().isPendingReturn(pos);
				assert m_LocalVarAssignmentAtCall.get(pos) == null;
				m_LocalVarAssignmentAtCall.put(pos, term);
			}
			
			public void putGlobalVarAssign(Integer pos, Term term) {
				assert m_TraceWF.getTrace().isCallPosition(pos);
				assert m_Terms[pos] == null;
				m_Terms[pos] = term;
			}
			
			public void putNonCallFormula(Integer pos, Term term) {
				assert !m_TraceWF.getTrace().isCallPosition(pos);
				assert m_Terms[pos] == null;
				m_Terms[pos] = term;
				
			}
			
			public void putPendingContext(Integer pendingReturnPos, Term term) {
				assert m_TraceWF.getTrace().isPendingReturn(pendingReturnPos);
				assert !m_PendingContexts.containsKey(pendingReturnPos);
				m_PendingContexts.put(pendingReturnPos, term);
			}
		}

}
