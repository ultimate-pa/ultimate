package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Check if a trace fulfills a specification. If the trace does, provide a Hoare
 * annotation as proof. 
 * <p>
 * Given <ul> 
 * <li> a precondition stated by predicate φ_0 
 * <li> a postcondition stated by predicate φ_n
 * <li> a trace (which is a word of CodeBlocks) cb_0 cb_2 ... cb_{n-1},
 * </ul>
 * check if the trace always fulfills the postcondition φ_n if the 
 * precondition φ_0 holds before the execution of the trace, i.e. we check if
 * the following inclusion of predicates is valid.
 * post(φ_0, cb_1 cb_2 ... cb_n) ⊆ φ_n
 * <p>
 * A feasibility check of a trace can be seen as the special case of this trace
 * check. A trace is feasible if and only if the trace does not fulfill the 
 * specification given by the precondition <i>true</i> and the postcondition
 * <i>false</i>. See Example1.
 * <p>
 * Example1: If <ul>
 * <li> the precondition is the predicate <i>true</i>,
 * <li> the postcondition is the predicate <i>false</i>,
 * <li> and the trace cb_0 cb_1 is x:=0; x!=-1;,
 * </ul><p>
 * then the trace fulfills its specification.
 * <p>
 * Example2: If <ul>
 * <li> the precondition is the predicate x==0,
 * <li> the postcondition is the predicate x==1,
 * <li> and the trace cb_0 cb_1 is x++; x++;,
 * </ul><p>
 * then the trace does not fulfill its specification.
 * <p>
 * If the trace fulfills its specification, we can provide a sequence of
 * inductive interpolants which is a sequence of predicates φ_i 0<1<n such the
 * inclusion post(φ_i, cb_i}) ⊆ φ_{i+1} holds for 0⩽i<n. This sequence of 
 * predicates can be seen as a Hoare annotation of this single trace.
 * <p>
 * If the trace contains calls and returns the TraceChecker will provide nested
 * interpolants.
 * <p>
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TraceChecker {
	
	protected static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	

	/**
	 * Interface for query the SMT solver. 
	 */
	protected final SmtManager m_SmtManager;
	
	
	/**
	 * Data structure that unifies Predicates with respect to its Term.
	 */
	protected PredicateUnifier m_PredicateUnifier;
	
	
	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure. The set of variables is represented as a map
	 * where the identifier of the variable is mapped to the type of the
	 * variable. 
	 */
	protected final ModifiableGlobalVariableManager m_ModifiedGlobals;
	
	
	/**
	 * Verbose debugging output is written to this PrintWriter. If null no
	 * debugging output is written.
	 */
	private final PrintWriter m_DebugPW;
	

	protected NestedWord<CodeBlock> m_Trace;
	protected IPredicate m_Precondition;
	protected IPredicate m_Postcondition;
	protected Map<Integer,IPredicate> m_PendingContexts;

//	protected NestedSsa m_AnnotatedSsa;
	protected AnnotateAndAsserter m_AAA;
	
	protected LBool m_IsSafe;
	protected IPredicate[] m_Interpolants;
	protected RcfgProgramExecution m_RcfgProgramExecution;
	
	
	
	/**
	 * Check if trace fulfills specification given by precondition and
	 * postcondition. 
	 * 
	 */
	public TraceChecker(IPredicate precondition, IPredicate postcondition,
			NestedWord<CodeBlock> trace,
			SmtManager smtManager,
						ModifiableGlobalVariableManager modifiedGlobals,
		 				PrintWriter debugPW) {
		m_SmtManager = smtManager;
		m_PredicateUnifier = new PredicateUnifier(m_SmtManager);
		m_ModifiedGlobals = modifiedGlobals;
		m_DebugPW = debugPW;
		SortedMap<Integer, IPredicate> pendingContexts = 
				new TreeMap<Integer, IPredicate>();
		checkTrace(precondition, postcondition, pendingContexts, trace);
	}
	
	
	/**
	 * Like three-argument-checkTrace-Method above but for traces which contain
	 * pending returns. The pendingContext maps the positions of pending returns
	 * to predicates which define possible variable valuations in the context to
	 * which the return leads the trace.
	 * 
	 */
	public TraceChecker(IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<CodeBlock> trace,
			SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			PrintWriter debugPW) {
		m_SmtManager = smtManager;
		m_PredicateUnifier = new PredicateUnifier(m_SmtManager);
		m_ModifiedGlobals = modifiedGlobals;
		m_DebugPW = debugPW;
		checkTrace(precondition, postcondition, pendingContexts, trace);
	}
	
	
	/**
	 * Returns 
	 * <ul> 
	 * <li> SAT if the trace does not fulfill its specification,
	 * <li> UNSAT if the trace does fulfill its specification,
	 * <li> UNKNOWN if it was not possible to determine if the trace fulfills
	 * its specification.
	 * </ul>
	 */
	public LBool isCorrect() {
		return m_IsSafe;		
	}
	
	
	
	/**
	 * Like three-argument-checkTrace-Method above but for traces which contain
	 * pending returns. The pendingContext maps the positions of pending returns
	 * to predicates which define possible variable valuations in the context to
	 * which the return leads the trace.
	 * 
	 */
	public LBool checkTrace(IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<CodeBlock> trace) {
		if (traceCheckRunning()) {
			throw new AssertionError("Each trace checker can check only one trace.");
		}
		m_Trace = trace;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PendingContexts = pendingContexts;
		
		m_SmtManager.startTraceCheck();
		NestedSsaBuilder nsb = 
				new NestedSsaBuilder(m_Trace, precondition, postcondition, 
						pendingContexts, m_SmtManager, m_ModifiedGlobals, m_DebugPW);
		NestedSsa ssa = nsb.getSsa();
		try {
			m_AAA = annotateAndAssert(ssa);
			m_IsSafe = m_AAA.isInputSatisfiable();
		} catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				m_IsSafe = LBool.UNKNOWN;
			}
			else {
				throw e;
			}
		}
		if (m_IsSafe==LBool.SAT) {
			DefaultTransFormulas dtf = new DefaultTransFormulas(m_Trace, 
					m_Precondition, m_Postcondition, pendingContexts, m_ModifiedGlobals);
			RelevantVariables relVars = new RelevantVariables(dtf);
			RcfgProgramExecutionBuilder rpeb = new RcfgProgramExecutionBuilder(m_ModifiedGlobals, (NestedWord<CodeBlock>) m_Trace, relVars);
			for (int i=0; i<m_Trace.length(); i++) {
				CodeBlock cb = m_Trace.getSymbolAt(i);
				TransFormula tf = cb.getTransitionFormulaWithBranchEncoders();
				if (tf.getBranchEncoders().size() > 0) {
					Map<TermVariable, Boolean> beMapping = new HashMap<TermVariable, Boolean>();
					for (TermVariable tv : tf.getBranchEncoders()) {
						String nameOfConstant = NestedSsaBuilder.branchEncoderConstantName(tv, i);
						Term indexedBe = m_SmtManager.getScript().term(nameOfConstant);
						Term value = getValue(indexedBe);
						Boolean booleanValue = getBooleanValue(value);
						beMapping.put(tv, booleanValue);
					}
					rpeb.setBranchEncoders(i, beMapping);
				}
			}
			for (BoogieVar bv : nsb.getIndexedVarRepresentative().keySet()) {
				if (!bv.getTermVariable().getSort().isArraySort()) {
					for (Integer index : nsb.getIndexedVarRepresentative().get(bv).keySet()) {
						Term indexedVar = nsb.getIndexedVarRepresentative().get(bv).get(index);
						Term valueT = getValue(indexedVar);
						Expression valueE = m_SmtManager.getBoogie2Smt().getSmt2Boogie().translate(valueT);
						rpeb.addValueAtVarAssignmentPosition(bv, index, valueE);
					}
				}
			}
			m_RcfgProgramExecution = rpeb.getRcfgProgramExecution();
		}
		return m_IsSafe;
	}
	
	protected AnnotateAndAsserter annotateAndAssert(NestedSsa ssa) {
		return new AnnotateAndAsserter(m_SmtManager, ssa);
	}
	
	
	private Term getValue(Term term) {
		Term[] arr = { term };
		Map<Term, Term> map = m_SmtManager.getScript().getValue(arr);
		Term value = map.get(term);
		return value;
	}
	
	private Boolean getBooleanValue(Term term) {
		Boolean result;
		Term trueTerm = m_SmtManager.getScript().term("true");
		if (term.equals(trueTerm)) {
			result = true;
		} else {
			Term falseTerm = m_SmtManager.getScript().term("false");
			if  (term.equals(falseTerm)) {
				result = false;
			} else {
				throw new AssertionError();
			}
		}
		return result;
	}

	
	


	

	
	/**
	 * Return a sequence of nested interpolants φ_1,...,φ_{n-1} that is 
	 * inductive for the trace, precondition φ_0, and postcondition φ_n that 
	 * were checked last. Interpolants are only available if the trace fulfilled
	 * its specification. The length of the returned sequence is the length of 
	 * the trace minus one.
	 * <p>
	 * For each two interpolants φ_i, φ_j which are similar (represented by the
	 * same term) the TraceChecker will use the same predicate. This means
	 * the returned array may contain the same object several times.<p>
	 * Furthermore throughout the lifetime of the TraceChecker, the TraceChecker
	 * will always use one predicate object for all interpolants which are
	 * similar (represented by the same term).<p>
	 * 
	 * @param interpolatedPositions Positions at which we compute interpolants.
	 * If interpolatedPositions==null each interpolant φ_0,...,φ_n is computed.
	 * Otherwise for each index i (but zero and n) that does not occur in 
	 * interpolatedPositions φ_i will be an UnknownPredicate.
	 * <p>
	 * interpolatedPositions has to be sorted (ascending) and its entries have
	 * to be smaller than or equal to m_Trace.size() 
	 * 
	 * @param predicateUnifier A PredicateUnifier in which precondition, 
	 * postcondition and all pending contexts are representatives.
	 */
	
	public void computeInterpolants(Set<Integer> interpolatedPositions,
										PredicateUnifier predicateUnifier) {
		m_PredicateUnifier = predicateUnifier;
		assert predicateUnifier.isRepresentative(m_Precondition);
		assert predicateUnifier.isRepresentative(m_Postcondition);
		for (IPredicate pred : m_PendingContexts.values()) {
			assert predicateUnifier.isRepresentative(pred);
		}
		computeInterpolants_Recursive(interpolatedPositions, predicateUnifier);
		
		boolean testRelevantVars = true;
		if (testRelevantVars) {
			RelevantVariables rv = new RelevantVariables(
					new DefaultTransFormulas(m_Trace, m_Precondition, m_Postcondition, null, m_ModifiedGlobals));
			for (int i=0; i<m_Interpolants.length; i++) {
				IPredicate itp = m_Interpolants[i];
				Set<BoogieVar> vars = itp.getVars();
				Set<BoogieVar> frel = rv.getForwardRelevantVariables()[i+1];
				Set<BoogieVar> brel = rv.getBackwardRelevantVariables()[i+1];
				assert (frel.containsAll(vars)) : "forward relevant variables wrong";
				assert (brel.containsAll(vars)) : "backward relevant variables wrong";;
			}
		}
	}
	
	public Word<CodeBlock> getTrace() {
		return m_Trace;
	}

	public IPredicate getPrecondition() {
		return m_Precondition;
	}

	public IPredicate getPostcondition() {
		return m_Postcondition;
	}

	public Map<Integer, IPredicate> getPendingContexts() {
		return m_PendingContexts;
	}

	public IPredicate[] getInterpolants() {
		assert m_Interpolants.length == m_Trace.length()-1;
		return m_Interpolants;
	}
	

	public RcfgProgramExecution getRcfgProgramExecution() {
		if (m_IsSafe == LBool.SAT || m_IsSafe == LBool.UNKNOWN) {
			return m_RcfgProgramExecution;
		} else {
			throw new AssertionError("only available if trace is feasible");
		}
	}


	/**
	 * Use tree interpolants to compute nested interpolants.
	 */
	private void computeInterpolants_Tree(Set<Integer> interpolatedPositions, 
			PredicateUnifier predicateUnifier) {
		m_PredicateUnifier = predicateUnifier;
		if (m_IsSafe != LBool.UNSAT) {
			throw new IllegalArgumentException(
				"Interpolants only available if trace fulfills specification");
		}
		if (m_Interpolants != null){
			throw new AssertionError("You already computed interpolants");
		}
		NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(
				m_SmtManager, m_AAA.getAnnotSSA(), m_PredicateUnifier, 
				interpolatedPositions, true);
		m_Interpolants = nib.getNestedInterpolants();
		assert !inductivityOfSequenceCanBeRefuted();
		assert m_Interpolants != null;
	}
	
	
	/**
	 * Use Matthias old naive interative method to compute nested interpolants.
	 * (Recursive interpolation queries, one for each call-return pair)
	 */
	private void computeInterpolants_Recursive(Set<Integer> interpolatedPositions,
			PredicateUnifier predicateUnifier) {
		m_PredicateUnifier = predicateUnifier;
		assert interpolatedPositions != null : "no interpolatedPositions";
		if (m_IsSafe != LBool.UNSAT) {
			if (m_IsSafe == null) {
				throw new AssertionError(
						"No trace check at the moment - no interpolants!");
			} else {
				throw new AssertionError(
						"Interpolants only available if trace fulfills specification");
			}
		}
		if (m_Interpolants != null){
			throw new AssertionError("You already computed interpolants");
		}

		
		List<Integer> nonPendingCallPositions = new ArrayList<Integer>();
		Set<Integer> newInterpolatedPositions = interpolatedPositionsForSubtraces(
								interpolatedPositions, nonPendingCallPositions);
		
		NestedInterpolantsBuilder nib = 
				new NestedInterpolantsBuilder(m_SmtManager,
						m_AAA.getAnnotSSA(), 
						m_PredicateUnifier, newInterpolatedPositions, false);
		m_Interpolants = nib.getNestedInterpolants();
		IPredicate oldPrecondition = m_Precondition;
		IPredicate oldPostcondition = m_Postcondition;
		
		if (!(m_Trace instanceof NestedWord)) {

			//forget trace - endTraceCheck already called
			if (m_Interpolants != null) { 
				assert !inductivityOfSequenceCanBeRefuted();
			}
		return;
		}
		
		NestedWord<CodeBlock> nestedTrace = (NestedWord<CodeBlock>) m_Trace;

		//forget trace - endTraceCheck already called
		if (m_Interpolants != null) { 
			assert !inductivityOfSequenceCanBeRefuted();
		}
		
		for (Integer nonPendingCall : nonPendingCallPositions) {
			//compute subtrace from to call to corresponding return
			int returnPosition = nestedTrace.getReturnPosition(nonPendingCall);
			NestedWord<CodeBlock> subtrace = 
					nestedTrace.getSubWord(nonPendingCall+1, returnPosition);

			Call call = (Call) nestedTrace.getSymbol(nonPendingCall);
			String calledMethod = call.getCallStatement().getMethodName();
			IPredicate oldVarsEquality = m_SmtManager.getOldVarsEquality(calledMethod);
			
			IPredicate precondition = m_PredicateUnifier.getOrConstructPredicate(
					oldVarsEquality.getFormula(), oldVarsEquality.getVars(), 
					oldVarsEquality.getProcedures());

			
			//Use a pendingContext the interpolant at the position before the
			//call, if this is -1 (because call is first codeBlock) use the
			//precondition used in this recursive interpolant computation one
			//level above
			SortedMap<Integer, IPredicate> pendingContexts = 
											new TreeMap<Integer,IPredicate>();
			IPredicate beforeCall;
			if (nonPendingCall == 0) {
				beforeCall = oldPrecondition;
			} else {
				beforeCall = m_Interpolants[nonPendingCall-1];
			}
			pendingContexts.put(subtrace.length()-1, beforeCall);
			
			//Check if subtrace is "compatible" with interpolants computed so
			//far. Obviously trace fulfills specification, but we need this
			//proof to be able to compute interpolants.
			IPredicate interpolantAtReturnPosition;
			if (returnPosition == nestedTrace.length()-1) {
				// special case: last position of trace is return
				// interpolant at this position is the postcondition
				// (which is stored in oldPostcondition, since m_Postcondition
				// is already set to null.
				interpolantAtReturnPosition = oldPostcondition;
				assert interpolantAtReturnPosition != null;
			} else {
				interpolantAtReturnPosition = m_Interpolants[returnPosition];
				assert interpolantAtReturnPosition != null;
			}

			TraceChecker tc = new TraceChecker(precondition, 
					interpolantAtReturnPosition, pendingContexts, subtrace, 
					m_SmtManager, m_ModifiedGlobals, m_DebugPW);
			LBool isSafe = tc.isCorrect();
			assert isSafe == LBool.UNSAT;
			
			//Compute interpolants for subsequence and add them to interpolants
			//computed by this TraceChecker
			tc.computeInterpolants_Recursive(interpolatedPositions, m_PredicateUnifier);
			IPredicate[] interpolantSubsequence = tc.getInterpolants();
					
			assert SmtManager.isDontCare(m_Interpolants[nonPendingCall]);
			m_Interpolants[nonPendingCall] = precondition;
			for (int i=0; i<interpolantSubsequence.length; i++) {
				assert SmtManager.isDontCare(m_Interpolants[nonPendingCall+1+i]);
				m_Interpolants[nonPendingCall+1+i] = interpolantSubsequence[i];
			}			
		}
	}
	
	

	/**
	 * Compute interpolated positions used in recursive interpolant computation 
	 */
	private Set<Integer> interpolatedPositionsForSubtraces(
										Set<Integer> interpolatedPositions, 
										List<Integer> nonPendingCallPositions) {
		if (!(m_Trace instanceof NestedWord)) {
			return interpolatedPositions;
		}
		
		Set<Integer> newInterpolatedPositions = new HashSet<Integer>();
	
		int currentContextStackDepth = 0;
		NestedWord<CodeBlock> nestedTrace = (NestedWord<CodeBlock>) m_Trace;
		for (int i=0; i<nestedTrace.length()-1 ; i++) {
			
			if (nestedTrace.isInternalPosition(i)) {
				if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}		
			} else if (nestedTrace.isCallPosition(i)) {
				if (nestedTrace.isPendingCall(i)) {
					if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
						newInterpolatedPositions.add(i);
					}		
				} else {
					//we need interpolant before call if currentContextStackDepth == 0
					if (currentContextStackDepth == 0) {
						nonPendingCallPositions.add(i);
					}
					currentContextStackDepth++;
					assert currentContextStackDepth > 0;				
				}
			} else if (nestedTrace.isReturnPosition(i)) {
				currentContextStackDepth--;
				// new need interpolant after return if currentContextStackDepth == 0
				if (currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}	
			} else {
				throw new AssertionError();
			}
		}
		return newInterpolatedPositions;		
	}
	
	
	
	/**
	 * After start of a trace check until the computation of interpolants or
	 * an error path, the SmtManager is locked. If you do not compute
	 * interpolants or an error path, use this method to unlock the SmtManager.
	 */
	public void unlockSmtManager() {
		if (!traceCheckRunning()) {
			throw new AssertionError("No trace checked before");
		}
		m_SmtManager.endTraceCheck();
		if (m_Interpolants != null) { 
			assert !inductivityOfSequenceCanBeRefuted();
		}
	}
	
	
	
	/**
	 * Return true if a trace was already checked.
	 */
	private boolean traceCheckRunning() {
		if (m_Trace == null) {
			assert m_Precondition == null;
			assert m_Postcondition == null;
			assert m_IsSafe == null;
			assert m_Interpolants == null;
			return false;
		} else {
			assert m_Precondition != null;
			assert m_Postcondition != null;
			assert m_IsSafe != null;
			return true;
		}
	}
	

	
	/**
	 * Return the locations of this trace.
	 * While using large block encoding this sequence is not unique.
	 * If <ul>
	 * <li> the trace does not fulfill its specification we return locations
	 * that correspond to a path which violated the specification.
	 * <li> we don't know if the traces fulfills its specification we return
	 * locations that might be a feasible path which violates the specification.
	 * <li> if the trace fulfills its specification we return any coherent
	 * sequence of locations.
	 */
	public List<CodeBlock> getFailurePath() {
		if (m_Trace == null) {
			throw new AssertionError("Check a trace first");
		}
		List<CodeBlock> result = 
				AnnotateAndAsserter.constructFailureTrace(m_Trace, m_SmtManager);
		unlockSmtManager();
		return result;
	}
	
	
	
	
	
	/**
	 * Return true iff m_Interpolants is an inductive sequence of nested 
	 * interpolants.
	 */
	private boolean inductivityOfSequenceCanBeRefuted() {
		boolean result = false;
		for (int i=0; i<m_Trace.length(); i++) {
			if (isCallPosition(i, m_Trace)) {
				LBool inductive = m_SmtManager.isInductiveCall(getInterpolant(i-1), 
						(Call) m_Trace.getSymbol(i), getInterpolant(i), true);
				result |= (inductive == LBool.SAT);
			}
			else if (isReturnPosition(i, m_Trace)) {
				IPredicate context;
				if (isPendingReturn(i, m_Trace)) {
					context = m_PendingContexts.get(i);
				} else {
					int callPosition = ((NestedWord<CodeBlock>) m_Trace).getCallPosition(i);
					context = getInterpolant(callPosition-1); 
				}			
				LBool inductive = m_SmtManager.isInductiveReturn(getInterpolant(i-1), context, 
						(Return) m_Trace.getSymbol(i), getInterpolant(i),true);
				result |= (inductive == LBool.SAT);
			}
			else {
				LBool inductive = m_SmtManager.isInductive(getInterpolant(i-1), m_Trace.getSymbol(i), 
						getInterpolant(i),true);
				result |= (inductive == LBool.SAT);
			}
			assert !result;
		}
		return result;
	}
	
	
	private IPredicate getInterpolant(int i) {
		if (i == -1) {
			return m_Precondition;
		} else if (i == m_Interpolants.length) {
			return m_Postcondition;
		} else {
			return m_Interpolants[i];
		}
	}
	
	
	private static boolean isCallPosition(int i, Word<CodeBlock> word) {
		if (word instanceof NestedWord) {
			return ((NestedWord<CodeBlock>) word).isCallPosition(i);
		} else {
			return false;
		}
	}
	
	private static boolean isReturnPosition(int i, Word<CodeBlock> word) {
		if (word instanceof NestedWord) {
			return ((NestedWord<CodeBlock>) word).isReturnPosition(i);
		} else {
			return false;
		}
	}
	
	private static boolean isPendingReturn(int i, Word<CodeBlock> word) {
		if (word instanceof NestedWord) {
			return ((NestedWord<CodeBlock>) word).isPendingReturn(i);
		} else {
			return false;
		}
	}
	
	
	/**
	 * Set<Integer> implementation that has only a contains method. The method
	 * always returns true;
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	public static class AllIntegers implements Set<Integer> {

		@Override
		public int size() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isEmpty() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean contains(Object o) {
			return true;
		}

		@Override
		public Iterator<Integer> iterator() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Object[] toArray() {
			throw new UnsupportedOperationException();
		}

		@Override
		public <T> T[] toArray(T[] a) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean add(Integer e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(Collection<? extends Integer> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}
		
	}
}