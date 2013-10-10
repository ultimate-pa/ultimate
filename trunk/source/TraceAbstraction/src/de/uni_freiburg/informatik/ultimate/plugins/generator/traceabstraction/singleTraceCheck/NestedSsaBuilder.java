package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class NestedSsaBuilder {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Script m_Script;
	final SmtManager m_SmtManager;
	final Stack<Map<BoogieVar,Term>> currentVersionStack =
									new Stack<Map<BoogieVar,Term>>();
	Map<BoogieVar,Term> currentLocalVarVersion;
	final Stack<Integer> startOfCallingContextStack =
									new Stack<Integer>();
	final Map<BoogieVar,Term> currentGlobalVarVersion =
									new HashMap<BoogieVar,Term>();
	Integer startOfCallingContext;
	
	final Map<BoogieVar,Map<Integer,Term>> m_IndexedVarRepresentative =
			new HashMap<BoogieVar,Map<Integer,Term>>();
	
	public Map<BoogieVar, Map<Integer, Term>> getIndexedVarRepresentative() {
		return m_IndexedVarRepresentative;
	}
	
	private final Map<Term,BoogieVar> m_Constants2BoogieVar = new HashMap<Term,BoogieVar>();

	private final TraceWithFormulas<TransFormula, IPredicate> m_TraceWF;
	
	private final SsaData m_SsaData;
	
	private class SsaData {
		
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
	
	private NestedSsa m_Ssa;
	
	private String m_currentProcedure;

	/**
	 * maps position of pending context to position of pending return
	 * the positions of pending contexts are -2,-3,-4,...
	 */
	private final Map<Integer,Integer> m_PendingContext2PendingReturn = 
			new HashMap<Integer,Integer>();
	

	public NestedSsaBuilder(NestedWord<CodeBlock> trace,
							SmtManager smtManager,
							DefaultTransFormulas defaultTransFormulas) {
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_TraceWF = defaultTransFormulas;
		m_SsaData = new SsaData();
		buildSSA();
	}
	


	private Term getVarVersion(BoogieVar varName, int index) {
		Map<Integer, Term> index2constant = m_IndexedVarRepresentative.get(varName);

		if (index2constant == null) {
			index2constant = new HashMap<Integer, Term>();
			m_IndexedVarRepresentative.put(varName,index2constant);
		}
		Term constant = index2constant.get(index);
		if (constant == null) {
			constant = m_SmtManager.getIndexedConstant(varName, index);
			index2constant.put(index, constant);
		}
		return constant;
	}



	private void buildSSA() {
		// add negative numbers <-1 for each pending context
		{
			int numberPendingContexts = m_TraceWF.getPendingContexts().size();
			List<Integer> pendingReturns;
			if (numberPendingContexts > 0) {
				pendingReturns = positionsOfPendingReturns(m_TraceWF.getTrace());
			} else {
				pendingReturns = new ArrayList<Integer>(0);
			}
			assert pendingReturns.size() == numberPendingContexts;
			
			startOfCallingContext = -1 - numberPendingContexts;
			currentLocalVarVersion = new HashMap<BoogieVar,Term>();
			
			for (int i=numberPendingContexts-1; i>=0; i--) {
				int pendingReturnPosition = pendingReturns.get(i);
				m_PendingContext2PendingReturn.put(startOfCallingContext, pendingReturnPosition);
				Return ret = (Return) m_TraceWF.getTrace().getSymbol(pendingReturnPosition);
				Call correspondingCall = ret.getCorrespondingCall();
				{
					ProgramPoint callPredecessor = (ProgramPoint) correspondingCall.getSource();
					m_currentProcedure = callPredecessor.getProcedure();
				}
				IPredicate pendingContext = m_TraceWF.getPendingContexts().get(pendingReturnPosition);
				Term versioneeredContext = versioneerPredicate(pendingContext);
				m_SsaData.putPendingContext(pendingReturnPosition, versioneeredContext);
				startOfCallingContextStack.push(startOfCallingContext);
				
				TransFormula localVarAssignment = correspondingCall.getTransitionFormula();
				VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
				initLocalVarsVV.versionInVars();
				
				String calledProcedure = correspondingCall.getCallStatement().getMethodName();
				TransFormula oldVarAssignment = m_TraceWF.getOldVarAssignment(pendingReturnPosition);
				VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				
				startOfCallingContext++;
				m_currentProcedure = calledProcedure;
				
				{
					//set var version for all modifiable globals
					// (for context switches by call this is done by the global variable assignment
					Set<BoogieVar> modifiable = m_TraceWF.getOldVarAssignment(pendingReturnPosition).getInVars().keySet();
					for (BoogieVar bv : modifiable) {
						setCurrentVarVersion(bv, startOfCallingContext);
					}
				}
		
				
				initOldVarsVV.versionAssignedVars(startOfCallingContext);
				initLocalVarsVV.versionAssignedVars(startOfCallingContext);
				
				m_SsaData.putOldVarAssign(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
				m_SsaData.putLocalVarAssign(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
			}
				
		}
		assert (startOfCallingContext == -1);
		
		CodeBlock firstCodeBlock = m_TraceWF.getTrace().getSymbolAt(0);
		m_currentProcedure = getProcedureofCodeBlock(firstCodeBlock);
		
		{
			Term versioneeredPrecondition = versioneerPredicate(m_TraceWF.getPrecondition());
			m_SsaData.setPrecondition(versioneeredPrecondition);
		}
		
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
				currentVersionStack.push(currentLocalVarVersion);
				currentLocalVarVersion = new HashMap<BoogieVar,Term>();
			}
			if (m_TraceWF.getTrace().isReturnPosition(i)) {
				Return ret = (Return) symbol;
				m_currentProcedure = ret.getCallerProgramPoint().getProcedure();
				if (m_TraceWF.getTrace().isPendingReturn(i)) {
					// start new context. here local variables get negative numbers
					assert currentVersionStack.isEmpty();
					currentLocalVarVersion = new HashMap<BoogieVar,Term>();
				} else {
					currentLocalVarVersion = currentVersionStack.pop();
				}
				startOfCallingContext = startOfCallingContextStack.pop();
			}
			tfVV.versionAssignedVars(i);
			tfVV.versionBranchEncoders(i);
			tfVV.replaceRemainingVariables();
			if (m_TraceWF.getTrace().isCallPosition(i)) {
				m_SsaData.putLocalVarAssign(i, tfVV.getVersioneeredTerm());
			}
			else {
				m_SsaData.putNonCallFormula(i, tfVV.getVersioneeredTerm());
			}
//			s_Logger.debug("Term"+i+": "+m_ssa[i]);
//			TermUnLet unflet = new FormulaUnLet();
//			s_Logger.debug("UnFletedTerm"+i+": "+unflet.unlet(m_ssa[i]));
		}
		
		{
			Term versioneeredPostcondition = versioneerPredicate(m_TraceWF.getPostcondition());
			m_SsaData.setPostcondition(versioneeredPostcondition);
		}
		
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
	
	public String getProcedureofCodeBlock(CodeBlock cb) {
		ProgramPoint pp = (ProgramPoint) cb.getSource();
		return pp.getProcedure();
	}
	
	public NestedSsa getSsa() {
		return m_Ssa;
	}
	
	
	/**
	 * Compute identifier of the Constant that represents the branch encoder tv
	 * at position pos.
	 */
	public static String branchEncoderConstantName(TermVariable tv, int pos) {
		String name = tv.getName() + "_" + pos;
		return name;
	}
	
	
	private Term versioneerPredicate(IPredicate predicate) {
		Term result;
		//Step1: replace program variables by constants with version number
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : predicate.getVars()) {
			TermVariable tv = bv.getTermVariable();
			Term var = getCurrentVarVersion(bv);
			m_Constants2BoogieVar.put(var, bv);
			replacees.add(tv);
			replacers.add(var);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[0]);
		Term[] values = replacers.toArray(new Term[0]);
		result = m_Script.let( vars , values, predicate.getFormula());

		//Step2: replace remaining free variables by fresh constants
		result = replaceFreeVariablesByFreshConstants(result);
		
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}
	

	/**
	 * Return a term where all free variables are replaced by constants that
	 * have not yet been defined. The m_SmtManager takes care of the constants
	 * "freshness" (have not yet been defined and will not be used the future). 
	 */
	public Term replaceFreeVariablesByFreshConstants(Term term) {
		TermVariable[] remainingfreeVars = term.getFreeVars();
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (TermVariable tv : remainingfreeVars) {
				Term var = m_SmtManager.getFreshConstant(tv);
				replacees.add(tv);
				replacers.add(var);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[0]);
		Term[] values = replacers.toArray(new Term[0]);
		Term result = m_Script.let( vars , values, term);
		return result;
	}
	
	
	
	private class VariableVersioneer {
		private final Map<BoogieVar,TermVariable> m_inVars;
		private final Map<BoogieVar,TermVariable> m_outVars;
		private final Set<BoogieVar> m_assignedVars;
		private final Set<TermVariable> m_BranchEncoders;
		private Term m_formula;
		private Set<TermVariable> letedVars = new HashSet<TermVariable>();
		
		public VariableVersioneer(TransFormula tf) {
			m_inVars = tf.getInVars();
			m_outVars = tf.getOutVars();
			m_assignedVars = tf.getAssignedVars();
			m_BranchEncoders = tf.getBranchEncoders();
			m_formula = tf.getFormula();
		}
		
		public void versionInVars() {
			for (BoogieVar name : m_inVars.keySet()) {
				TermVariable tv = m_inVars.get(name);
				Term var = getCurrentVarVersion(name);
				m_Constants2BoogieVar.put(var, name);
				TermVariable[] vars = { tv }; 
				Term[] values = { var };
				m_formula = m_Script.let(vars, values, m_formula);
				letedVars.add(tv);
			}
		}

		//oldvar may never occur as assigned Var
		public void versionAssignedVars(int currentPos) {
			for (BoogieVar name : m_assignedVars) {
				TermVariable tv = m_outVars.get(name);
				Term var = setCurrentVarVersion(name,currentPos);
				TermVariable[] vars = { tv }; 
				Term[] values = { var };
				m_formula = m_Script.let(vars, values, m_formula);
				letedVars.add(tv);
				m_Constants2BoogieVar.put(var, name);
			}
		}
		

		
		public void versionBranchEncoders(int currentPos) {
			ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
			ArrayList<Term> replacers = new ArrayList<Term>();
			for (TermVariable tv : m_BranchEncoders) {
				String name = branchEncoderConstantName(tv, currentPos);
				m_Script.declareFun(name, new Sort[0], tv.getSort());
				replacees.add(tv);
				replacers.add(m_Script.term(name));
			}
			TermVariable[] vars = replacees.toArray(new TermVariable[0]);
			Term[] values = replacers.toArray(new Term[0]);
			m_formula = m_Script.let( vars , values, m_formula);
		}
		
		public void replaceRemainingVariables() {
			m_formula = replaceFreeVariablesByFreshConstants(m_formula);
		}

		
		public Term getVersioneeredTerm() {
			return (new FormulaUnLet()).unlet(m_formula);
		}
	}
		
		
		
		private Term getCurrentVarVersion(BoogieVar bv) {
			if (bv.isOldvar()) {
				return getVarVersion(bv, startOfCallingContext);
//				if (currentGlobalVarVersion.containsKey(bv)) {
//					return currentGlobalVarVersion.get(bv);
//				} else {
//					return setCurrentVarVersion(bv, startOfCallingContext);
//				}
			} else if (bv.isGlobal()) {
				if (currentGlobalVarVersion.containsKey(bv)) {
					return currentGlobalVarVersion.get(bv);
				}
				else {
					if (modifiedInCurrentCallingContext(bv)) {
						// this is the assignment at the call position
						return setCurrentVarVersion(bv, startOfCallingContext);
					} else {
						// this global variable is not modified by any procedure
						// in this trace
						return setCurrentVarVersion(bv, -1);
					}
					
				}
			} else { //case varName is no global var
				if (currentLocalVarVersion.containsKey(bv)) {
					return currentLocalVarVersion.get(bv);
				}
				else {
					return getVarVersion(bv, startOfCallingContext);
				}
			}
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


		private Term setCurrentVarVersion(BoogieVar varName, int index) {
			Term var = getVarVersion(varName, index);
			if (varName.isGlobal()) {
				assert (!varName.isOldvar() || index == startOfCallingContext) :
					"oldVars may only be assigned at entry of procedure";
				currentGlobalVarVersion.put(varName, var);
			}
			else {
				currentLocalVarVersion.put(varName,var);
			}
			return var; 
		}

		
		@Deprecated //pendingContexts is now Map
		private List<Integer> positionsOfPendingReturns(NestedWord<CodeBlock> nw) {
			List<Integer> result = new ArrayList<Integer>();
			for (int i=0; i<nw.length(); i++) {
				if (nw.isPendingReturn(i)) {
					result.add(i);
				}
			}
			return result;
		}
	

}
