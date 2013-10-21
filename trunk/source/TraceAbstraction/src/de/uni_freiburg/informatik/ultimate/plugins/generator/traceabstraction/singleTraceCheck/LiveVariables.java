package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder.VariableVersioneer;

/**
 * TODO: documentation
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class LiveVariables extends NestedSsaBuilder {
	private Collection<Term>[] m_ConstantsForEachPosition;
	private Set<Term>[] m_LiveConstants;
	private Set<Term>[] m_ForwardLiveConstants;
	private Set<Term>[] m_BackwardLiveConstants;
	private Set<BoogieVar>[] m_LiveVariables;
	
	public LiveVariables(NestedWord<CodeBlock> trace,
			SmtManager smtManager,
			DefaultTransFormulas defaultTransFormulas) {
		super(trace, smtManager, defaultTransFormulas);
		computeLiveVariables();
	}
	
	


	@Override
	protected void buildSSA() {
		// Initialize members
		m_ConstantsForEachPosition = new Collection[m_TraceWF.getTrace().length() + 2];
		m_LiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_ForwardLiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_BackwardLiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_LiveVariables = new Set[m_ConstantsForEachPosition.length];
		
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
		
		assert m_ConstantsForEachPosition != null;
		m_ConstantsForEachPosition[0] = precondVV.getSubstitutionMapping().values();
		
		
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
			m_ConstantsForEachPosition[i+1] = tfVV.getSubstitutionMapping().values();
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
		

		m_ConstantsForEachPosition[m_ConstantsForEachPosition.length - 1] = 
				postCondVV.getSubstitutionMapping().values();

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




	private void computeLiveVariables() {
		computeForwardLiveConstants();
		computeBackwardLiveConstants();
		assert m_LiveConstants != null;
		// Compute live constants using forward live constants and backward live constants.
		for (int i = 0; i < m_ConstantsForEachPosition.length; i++) {
			assert m_LiveConstants[i] == null : "Live constants already computed!";
			m_ForwardLiveConstants[i].retainAll(m_BackwardLiveConstants[i]);
			m_LiveConstants[i] = m_ForwardLiveConstants[i];
		}
		
		generateLiveVariablesFromLiveConstants();
	}
	
	private void generateLiveVariablesFromLiveConstants() {
		assert m_LiveVariables != null;
		m_LiveVariables[0] = new HashSet<BoogieVar>();
		for (int i = 1; i < m_ConstantsForEachPosition.length; i++) {
			Set<BoogieVar> liveVars = new HashSet<BoogieVar>();
			for (Term t : m_LiveConstants[i]) {
				liveVars.add(m_Constants2BoogieVar.get(t));
			}
			m_LiveVariables[i] = liveVars;
		}
	}

		
	private void computeForwardLiveConstants() {
		assert m_ForwardLiveConstants != null;
		assert m_ConstantsForEachPosition != null;
		m_ForwardLiveConstants[0] = new HashSet<Term>();
		for (int i = 1; i < m_ConstantsForEachPosition.length; i++) {
			Set<Term> flc = new HashSet<Term>();
			assert m_ForwardLiveConstants[i-1] != null;
			flc.addAll(m_ForwardLiveConstants[i-1]);
			flc.addAll(m_ConstantsForEachPosition[i]);
			m_ForwardLiveConstants[i] = flc;
		}
	}
	
	private void computeBackwardLiveConstants() {
		assert m_BackwardLiveConstants != null;
		m_BackwardLiveConstants[m_ConstantsForEachPosition.length - 1] = 
				new HashSet<Term>();
		for (int i = m_ConstantsForEachPosition.length - 2; i >= 0; i--) {
			Set<Term> blc = new HashSet<Term>();
			assert m_BackwardLiveConstants[i+1] != null;
			blc.addAll(m_BackwardLiveConstants[i+1]);
			blc.addAll(m_ConstantsForEachPosition[i]);
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
