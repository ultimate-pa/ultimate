package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
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
	final PrintWriter m_IterationPW;
	
	final Map<BoogieVar,Map<Integer,Term>> m_IndexedVarRepresentative =
			new HashMap<BoogieVar,Map<Integer,Term>>();
	
	public Map<BoogieVar, Map<Integer, Term>> getIndexedVarRepresentative() {
		return m_IndexedVarRepresentative;
	}


	private final IPredicate m_Precondition;
	private final IPredicate m_Postcondition;
	private final Map<Integer, IPredicate> m_PendingContexts;
	
	private final NestedSsa m_Ssa;
	
	private String m_currentProcedure;
	
	
	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure.
	 */
	private final ModifiableGlobalVariableManager m_ModifiedGlobals;

	@SuppressWarnings("unchecked")
	public NestedSsaBuilder(Word<CodeBlock> counterexample,
							IPredicate precondition,
							IPredicate postcondition,
							Map<Integer, IPredicate> pendingContexts,
							SmtManager smtManager,
							ModifiableGlobalVariableManager modifiedGlobals,
						 	PrintWriter iterationPW) {
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PendingContexts = pendingContexts;
		 
		m_Ssa  = new NestedSsa(
				NestedWord.nestedWord(counterexample),
				new Term[counterexample.length()],
				new HashMap<Integer,Term>(),
				new HashMap<Integer,Term>(),
				new TreeMap<Integer,Term>(),
				new HashMap<Term, BoogieVar>());
		m_IterationPW = iterationPW;
		m_ModifiedGlobals = modifiedGlobals;
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
			int numberPendingContexts = m_PendingContexts.size();
			List<Integer> pendingReturns;
			if (numberPendingContexts > 0) {
				pendingReturns = positionsOfPendingReturns(m_Ssa.getTrace());
			} else {
				pendingReturns = new ArrayList<Integer>(0);
			}
			assert pendingReturns.size() == numberPendingContexts;
			
			startOfCallingContext = -1 - numberPendingContexts;
			currentLocalVarVersion = new HashMap<BoogieVar,Term>();
			
			for (int i=numberPendingContexts-1; i>=0; i--) {
				int pendingReturnPosition = pendingReturns.get(i);
				Return ret = (Return) m_Ssa.getTrace().getSymbol(pendingReturnPosition);
				Call correspondingCall = ret.getCorrespondingCall();
				{
					ProgramPoint callPredecessor = (ProgramPoint) correspondingCall.getSource();
					m_currentProcedure = callPredecessor.getProcedure();
				}
				Term versioneeredContext = versioneerPredicate(m_PendingContexts.get(pendingReturnPosition));
				m_Ssa.getPendingContexts().put(pendingReturnPosition, versioneeredContext);
				startOfCallingContextStack.push(startOfCallingContext);
				
				TransFormula localVarAssignment = correspondingCall.getTransitionFormula();
				VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
				initLocalVarsVV.versionInVars();
				
				String calledProcedure = correspondingCall.getCallStatement().getMethodName();
				TransFormula oldVarAssignment = m_ModifiedGlobals.getOldVarsAssignment(calledProcedure);
				VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				
				startOfCallingContext++;
				m_currentProcedure = calledProcedure;
				
				{
					//set var version for all modifiable globals
					// (for context switches by call this is done by the global variable assignment
					Set<BoogieVar> modifiable = m_ModifiedGlobals.getModifiedBoogieVars(m_currentProcedure);
					for (BoogieVar bv : modifiable) {
						setCurrentVarVersion(bv, startOfCallingContext);
					}
				}
		
				
				initOldVarsVV.versionAssignedVars(startOfCallingContext);
				initLocalVarsVV.versionAssignedVars(startOfCallingContext);
				
				m_Ssa.getGlobalOldVarAssignmentAtCall().put(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
				m_Ssa.getLocalVarAssignmentAtCall().put(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
			}
				
		}
		assert (startOfCallingContext == -1);
		
		CodeBlock firstCodeBlock = m_Ssa.getTrace().getSymbolAt(0);
		ProgramPoint pp = (ProgramPoint) firstCodeBlock.getSource();
		m_currentProcedure = pp.getProcedure();
		
		{
			Term versioneeredPrecondition = versioneerPredicate(m_Precondition);
			m_Ssa.setPrecondition(versioneeredPrecondition);
		}
		
		for (int i=0; i<m_Ssa.getTrace().length(); i++) {
			CodeBlock symbol = m_Ssa.getTrace().getSymbolAt(i);
			assert (!(symbol instanceof GotoEdge)) : "TraceChecker does not support GotoEdges";
			
			TransFormula tf = symbol.getTransitionFormulaWithBranchEncoders();
			
			VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();
			
			if (m_Ssa.getTrace().isCallPosition(i)) {
				Call call = (Call) symbol;
				String calledProcedure = call.getCallStatement().getMethodName();
				m_currentProcedure = calledProcedure;
				TransFormula oldVarAssignment = m_ModifiedGlobals.getOldVarsAssignment(calledProcedure);
				VariableVersioneer initOldVarsVV = 
											new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				startOfCallingContextStack.push(startOfCallingContext);
				startOfCallingContext = i;
				initOldVarsVV.versionAssignedVars(i);
				m_Ssa.getGlobalOldVarAssignmentAtCall().put(i, initOldVarsVV.getVersioneeredTerm());

				TransFormula globalVarAssignment = m_ModifiedGlobals.getGlobalVarsAssignment(calledProcedure);
				VariableVersioneer initGlobalVarsVV = 
						new VariableVersioneer(globalVarAssignment);
				initGlobalVarsVV.versionInVars();
				initGlobalVarsVV.versionAssignedVars(i);
				m_Ssa.getFormulas()[i] = initGlobalVarsVV.getVersioneeredTerm();
				currentVersionStack.push(currentLocalVarVersion);
				currentLocalVarVersion = new HashMap<BoogieVar,Term>();
			}
			if (m_Ssa.getTrace().isReturnPosition(i)) {
				Return ret = (Return) symbol;
				m_currentProcedure = ret.getCallerProgramPoint().getProcedure();
				if (m_Ssa.getTrace().isPendingReturn(i)) {
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
			if (m_Ssa.getTrace().isCallPosition(i)) {
				m_Ssa.getLocalVarAssignmentAtCall().put(i, tfVV.getVersioneeredTerm());
			}
			else {
				m_Ssa.getFormulas()[i] = tfVV.getVersioneeredTerm();
			}
//			s_Logger.debug("Term"+i+": "+m_ssa[i]);
//			TermUnLet unflet = new FormulaUnLet();
//			s_Logger.debug("UnFletedTerm"+i+": "+unflet.unlet(m_ssa[i]));
		}
		
		{
			Term versioneeredPostcondition = versioneerPredicate(m_Postcondition);
			m_Ssa.setPostcondition(versioneeredPostcondition);
		}
		
		
		if (m_IterationPW != null) {
			dumpSSA();
		}
	}
	
	public NestedSsa getSsa() {
		return m_Ssa;
	}
	
	
	
	private void dumpSSA() {
		String line;
		int indentation = 0;
		FormulaUnLet unflet = new FormulaUnLet();
		try {
			line = "===== Nested SSA =====";
			s_Logger.debug(line);
			m_IterationPW.println(line);
			for (int i=0; i<m_Ssa.getTrace().length(); i++) {
				if (m_Ssa.getTrace().isCallPosition(i)) {
					indentation++;
					line = AbstractCegarLoop.addIndentation(indentation, 
							"LocalVariableAssignment"+i+": "+unflet.unlet(
										m_Ssa.getLocalVarAssignmentAtCall().get(i)).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					line = AbstractCegarLoop.addIndentation(indentation, 
							"GlobalOld-VariableAssignment"+i+": "+unflet.unlet(
									m_Ssa.getGlobalOldVarAssignmentAtCall().get(i)).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					line = AbstractCegarLoop.addIndentation(indentation, 
							"GlobalVariableAssignment"+i+": "+unflet.unlet(
									m_Ssa.getFormulas()[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
				} else if (m_Ssa.getTrace().isReturnPosition(i)) {
					line = AbstractCegarLoop.addIndentation(indentation, 
							"LocalVariableAssignment"+i+": "+unflet.unlet(
									m_Ssa.getFormulas()[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					indentation--;
				} else 	{
					line = AbstractCegarLoop.addIndentation(indentation, 
						"Term "+i+": "+unflet.unlet(m_Ssa.getFormulas()[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
				}
			}
			m_IterationPW.println("");
			m_IterationPW.println("");
		} finally {
			m_IterationPW.flush();
		}
	}
	
	
	
	
	
	private Term versioneerPredicate(IPredicate predicate) {
		Term result;
		//Step1: replace program variables by constants with version number
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : predicate.getVars()) {
			TermVariable tv = bv.getTermVariable();
			Term var = getCurrentVarVersion(bv);
			m_Ssa.getConstants2BoogieVar().put(var, bv);
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
				m_Ssa.getConstants2BoogieVar().put(var, name);
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
				m_Ssa.getConstants2BoogieVar().put(var, name);
			}
		}
		

		
		public void versionBranchEncoders(int currentPos) {
			ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
			ArrayList<Term> replacers = new ArrayList<Term>();
			for (TermVariable tv : m_BranchEncoders) {
				String name = tv.getName() + "_" + currentPos;
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
				if (modifiedInCurrentCallingContext(bv)){
					return getVarVersion(bv, startOfCallingContext);
				} else {
					// use the nonOldVersion
					return getCurrentVarVersion(m_SmtManager.getNonOldVar(bv));
				}
			}
			else if (bv.isGlobal()) {
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
			}
			else { //case varName is no global var
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
			boolean isModified;
			if (bv.isOldvar()) {
				isModified = m_ModifiedGlobals.
					getOldVarsAssignment(m_currentProcedure).getAssignedVars().contains(bv);
			} else {
				isModified = m_ModifiedGlobals.
					getGlobalVarsAssignment(m_currentProcedure).getAssignedVars().contains(bv);
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
