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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


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
	protected final PredicateBuilder m_PredicateBuilder;
	
	
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
	

	protected Word<CodeBlock> m_Trace;
	protected IPredicate m_Precondition;
	protected IPredicate m_Postcondition;
	protected Map<Integer,IPredicate> m_PendingContexts;

	protected NestedSsa m_AnnotatedSsa;
	
	protected LBool m_IsSafe;
	protected IPredicate[] m_Interpolants;
	
	
	public TraceChecker(SmtManager smtManager,
						ModifiableGlobalVariableManager modifiedGlobals,
		 				Map<String,ProgramPoint> proc2entry,
		 				PrintWriter debugPW) {
		m_SmtManager = smtManager;
		m_PredicateBuilder = new PredicateBuilder();
		m_ModifiedGlobals = modifiedGlobals;
		m_DebugPW = debugPW;
	}
	
	private TraceChecker(SmtManager smtManager,
						 ModifiableGlobalVariableManager modifiedGlobals, 
		 				 PrintWriter debugPW, PredicateBuilder 
		 				 predicateBuilder) {
		m_SmtManager = smtManager;
		m_PredicateBuilder = predicateBuilder;
		m_ModifiedGlobals = modifiedGlobals;
		m_DebugPW = debugPW;
	}
	
	



	/**
	 * Check if trace fulfills specification given by precondition and
	 * postcondition. Returns 
	 * <ul> 
	 * <li> SAT if the trace does not fulfill its specification,
	 * <li> UNSAT if the trace does fulfill its specification,
	 * <li> UNKNOWN if it was not possible to determine if the trace fulfills
	 * its specification.
	 * </ul>
	 * 
	 */
	public LBool checkTrace(IPredicate precondition, IPredicate postcondition,
														Word<CodeBlock> trace) {
		Map<Integer, IPredicate> pendingContexts = new HashMap<Integer, IPredicate>(0);
		return checkTrace(precondition, postcondition, pendingContexts, trace);
	}
	
	
	
	/**b
	 * Like three-argument-checkTrace-Method above but for traces which contain
	 * pending returns. The pendingContext maps the positions of pending returns
	 * to predicates which define possible variable valuations in the context to
	 * which the return leads the trace.
	 * 
	 */
	public LBool checkTrace(IPredicate precondition, IPredicate postcondition,
			Map<Integer, IPredicate> pendingContexts, Word<CodeBlock> trace) {
		if (traceCheckRunning()) {
			throw new AssertionError("Forget current trace to be able to check new one");
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
			AnnotateAndAsserter aaa = new AnnotateAndAsserter(m_SmtManager, ssa, m_Trace);
			m_AnnotatedSsa = aaa.getAnnotSSA();
			m_IsSafe = aaa.isInputSatisfiable();
		} catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				m_IsSafe = LBool.UNKNOWN;
			}
			else {
				throw e;
			}
		}
		if (m_IsSafe==LBool.SAT) {
			s_Logger.debug("Valuations of some variables");
			HashSet<Term> terms = new HashSet<Term>();
			for (Term t : ssa.getConstants2BoogieVar().keySet())
				if (!t.getSort().isArraySort())
					terms.add(t);
			Term[] allTerms = terms.toArray(new Term[terms.size()]);
			try {
				Map<Term, Term> val = m_SmtManager.getScript().getValue(allTerms);
				for (Term term : allTerms) {
					s_Logger.debug(new DebugMessage("Value of {0}: {1}", term, val.get(term)));
				}
			} catch (SMTLIBException e) {
				s_Logger.debug("Valuation not available.");
				s_Logger.debug(e.getMessage());
			}
		}
		return m_IsSafe;
	}
	
	
	
	/**
	 * Returns a predicate which states that old(g)=g for all global variables
	 * g that are modified by procedure proc. 
	 */
	public IPredicate getOldVarsEquality(String proc) {
		Set<BoogieVar> modifiableGlobals = m_ModifiedGlobals.getModifiedBoogieVars(proc);
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Term term = m_SmtManager.getScript().term("true");
			for (BoogieVar bv : modifiableGlobals) {
				vars.add(bv);
				BoogieVar bvOld = m_SmtManager.getBoogieVar2SmtVar()
						.getOldGlobals().get(bv.getIdentifier());
				vars.add(bvOld);
				TermVariable tv = bv.getTermVariable();
				TermVariable tvOld = bvOld.getTermVariable();
				Term equality = m_SmtManager.getScript().term("=", tv, tvOld);
				term = Util.and(m_SmtManager.getScript(), term, equality);
			}

		IPredicate result = m_PredicateBuilder.getOrConstructPredicate(
											term, vars, new HashSet<String>(0));
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
	 */
	
	public IPredicate[] getInterpolants(Set<Integer> interpolatedPositions) {
		return getInterpolants_Recursive(interpolatedPositions);
	}
	
	
	/**
	 * Use tree interpolants to compute nested interpolants.
	 */
	private IPredicate[] getInterpolants_Tree(Set<Integer> interpolatedPositions) {
		if (m_IsSafe != LBool.UNSAT) {
			throw new IllegalArgumentException(
				"Interpolants only available if trace fulfills specification");
		}
		if (m_Interpolants != null){
			throw new AssertionError("You already computed interpolants");
		}
		m_PredicateBuilder.declarePredicate(m_Precondition);
		m_PredicateBuilder.declarePredicate(m_Postcondition);
		NestedInterpolantsBuilder nib = 
				new NestedInterpolantsBuilder(m_SmtManager,
						m_AnnotatedSsa, 
							m_PredicateBuilder, interpolatedPositions, true);
		m_Interpolants = nib.getNestedInterpolants();
		assert !inductivityOfSequenceCanBeRefuted();
		m_Trace = null;
		m_Precondition = null;
		m_Postcondition = null;
		m_IsSafe = null;
		assert m_Interpolants != null;
		return m_Interpolants;
	}
	
	
	/**
	 * Use Matthias old naive interative method to compute nested interpolants.
	 * (Recursive interpolation queries, one for each call-return pair)
	 */
	private IPredicate[] getInterpolants_Recursive(Set<Integer> interpolatedPositions) {
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
		m_PredicateBuilder.declarePredicate(m_Precondition);
		m_PredicateBuilder.declarePredicate(m_Postcondition);

		
		List<Integer> nonPendingCallPositions = new ArrayList<Integer>();
		Set<Integer> newInterpolatedPositions = interpolatedPositionsForSubtraces(
								interpolatedPositions, nonPendingCallPositions);
		
		NestedInterpolantsBuilder nib = 
				new NestedInterpolantsBuilder(m_SmtManager,
						m_AnnotatedSsa, 
						m_PredicateBuilder, newInterpolatedPositions, false);
		m_Interpolants = nib.getNestedInterpolants();
		IPredicate oldPrecondition = m_Precondition;
		IPredicate oldPostcondition = m_Postcondition;
		
		if (!(m_Trace instanceof NestedWord)) {

			//forget trace - endTraceCheck already called
			if (m_Interpolants != null) { 
				assert !inductivityOfSequenceCanBeRefuted();
			}
			m_Trace = null;
			m_Precondition = null;
			m_Postcondition = null;
			m_IsSafe = null;
			
			return m_Interpolants;
		}
		
		NestedWord<CodeBlock> nestedTrace = (NestedWord<CodeBlock>) m_Trace;

		//forget trace - endTraceCheck already called
		if (m_Interpolants != null) { 
			assert !inductivityOfSequenceCanBeRefuted();
		}
		m_Trace = null;
		m_Precondition = null;
		m_Postcondition = null;
		m_IsSafe = null;
		
		
		for (Integer nonPendingCall : nonPendingCallPositions) {
			//compute subtrace from to call to corresponding return
			int returnPosition = nestedTrace.getReturnPosition(nonPendingCall);
			NestedWord<CodeBlock> subtrace = 
					nestedTrace.getSubWord(nonPendingCall+1, returnPosition);

			Call call = (Call) nestedTrace.getSymbol(nonPendingCall);
			String calledMethod = call.getCallStatement().getMethodName();
			IPredicate precondition = getOldVarsEquality(calledMethod);

			TraceChecker tc = new TraceChecker(m_SmtManager, 
												m_ModifiedGlobals, 
												m_DebugPW, m_PredicateBuilder);
			
			//Use a pendingContext the interpolant at the position before the
			//call, if this is -1 (because call is first codeBlock) use the
			//precondition used in this recursive interpolant computation one
			//level above
			Map<Integer, IPredicate> pendingContexts = 
											new HashMap<Integer,IPredicate>(1);
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
			LBool isSafe = tc.checkTrace(precondition, interpolantAtReturnPosition 
					, pendingContexts, subtrace);
			assert isSafe == LBool.UNSAT;
			
			//Compute interpolants for subsequence and add them to interpolants
			//computed by this TraceChecker
			IPredicate[] interpolantSubsequence = 
					tc.getInterpolants_Recursive(interpolatedPositions);
			assert SmtManager.isDontCare(m_Interpolants[nonPendingCall]);
			m_Interpolants[nonPendingCall] = precondition;
			for (int i=0; i<interpolantSubsequence.length; i++) {
				assert SmtManager.isDontCare(m_Interpolants[nonPendingCall+1+i]);
				m_Interpolants[nonPendingCall+1+i] = interpolantSubsequence[i];
			}			
		}
		IPredicate[] result = m_Interpolants;
		m_Interpolants = null;
		return result;
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
	 * Forget the trace which is checked at the moment. (Only then we are able
	 * to check the next trace)
	 */
	public void forgetTrace() {
		if (!traceCheckRunning()) {
			throw new AssertionError("No trace checked before");
		}
		m_SmtManager.endTraceCheck();
		if (m_Interpolants != null) { 
			assert !inductivityOfSequenceCanBeRefuted();
		}
		m_Trace = null;
		m_Precondition = null;
		m_Postcondition = null;
		m_IsSafe = null;
//		m_Interpolants = null;
	}
	
	
	
	/**
	 * Return true if a trace is checked at the moment 
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
		forgetTrace();
		return result;
	}
	
	
	
	
	
	/**
	 * Data structure that stores for each term a unique predicate.
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	class PredicateBuilder {
		
		private final Map<Term, IPredicate> m_Term2Predicates = 
												new HashMap<Term, IPredicate>();
		
		/**
		 * Add the pair (predicate.getFormula(), predicate) to the 
		 * term2Predicate mapping if this pair is not already contained.
		 * Throw an exception if there is already a different predicate assigned
		 * to the term predicate.getFormula.  
		 */
		void declarePredicate(IPredicate predicate) {
			Term term = predicate.getFormula();
			IPredicate storedPredicate = m_Term2Predicates.get(term);
			if (storedPredicate == null) {
				m_Term2Predicates.put(term, predicate);
			} else {
				if (storedPredicate != predicate) {
					throw new AssertionError("There is already a" +
							" different predicate for this term");
				}
			}
		}
		
		/**
		 * Get the predicate for term. If there is not yet a predicate for term,
		 * construct the predicate using vars.
		 * @param vars The BoogieVars of the TermVariables contained in term.
		 * @param proc All procedures of which vars contains local variables.
		 */
		IPredicate getOrConstructPredicate(Term term, 
											Set<BoogieVar> vars, Set<String> procs) {
			if (term instanceof AnnotatedTerm) {
				AnnotatedTerm annotatedTerm = (AnnotatedTerm) term;
				Annotation[] annotations = annotatedTerm.getAnnotations();
				if (annotations.length == 1) {
					if (annotations[0].getKey().equals(":quoted")) {
						term = annotatedTerm.getSubterm();
					} else {
						throw new UnsupportedOperationException();
					}
				} else {
					throw new UnsupportedOperationException();
				}
			}

			IPredicate p = m_Term2Predicates.get(term);
			if (p != null) {
				return p;
			}  
			ArrayList<IPredicate> impliedInterpolants = new ArrayList<IPredicate>();
			ArrayList<IPredicate> expliedInterpolants = new ArrayList<IPredicate>();
			p = getEquivalentPredicate(term, vars, procs, 
									impliedInterpolants, expliedInterpolants);
			if (p != null) {
				return p;
			}  
			SimplifyDDA simplifyDDA = 
					new SimplifyDDA(m_SmtManager.getScript(),s_Logger);
			Term simplifiedTerm = simplifyDDA.getSimplifiedTerm(term);
			if (simplifiedTerm == term) {
				//no simplification possible
				return addNewPredicate(term, vars, procs);
			} else {
				if (m_Term2Predicates.containsKey(simplifiedTerm)) {
					// this case can occur only if theorem prover says UNKNOWN
					// on equivalence checks
					return m_Term2Predicates.get(simplifiedTerm);
				}
				HashSet<TermVariable> tvs = new HashSet<TermVariable>();
				for (TermVariable tv : simplifiedTerm.getFreeVars()) {
					tvs.add(tv);
				}
				Set<BoogieVar> newVars = new HashSet<BoogieVar>();
				Set<String> newProcs = new HashSet<String>();
				for (BoogieVar bv : vars) {
					if (tvs.contains(bv.getTermVariable())) {
						newVars.add(bv);
						if (bv.getProcedure() != null) {
							newProcs.add(bv.getProcedure());
						}
					}
				}
				return addNewPredicate(simplifiedTerm, newVars, newProcs);
			}

		}
		
		private IPredicate addNewPredicate(Term term, Set<BoogieVar> vars, 
															Set<String> procs) {
			assert !m_Term2Predicates.containsKey(term);
			IPredicate predicate;
			if (equivalentToTrue(term)) {
				Term trueTerm = m_SmtManager.getScript().term("true");
				predicate = m_Term2Predicates.get(trueTerm);
				if (predicate == null) {
					predicate = m_SmtManager.newTruePredicate();
				}
				s_Logger.warn("Interpolant was equivalent to true");
			} else if (equivalentToFalse(term)){
				Term falseTerm = m_SmtManager.getScript().term("false");
				predicate = m_Term2Predicates.get(falseTerm);
				if (predicate == null) {
					predicate = m_SmtManager.newFalsePredicate();
				}
				s_Logger.warn("Interpolant was equivalent to false");
			} else {
				String[] procedures = procs.toArray(new String [0]);
//				ProgramPoint entryOfPredicatesProcedure = null;
//				if (proc != null) {
//					entryOfPredicatesProcedure = m_Proc2Entry.get(proc);
//					assert entryOfPredicatesProcedure != null;
//				}
				Term closedTerm = SmtManager.computeClosedFormula(
										term, vars, m_SmtManager.getScript());
				predicate = m_SmtManager.newPredicate(
										term, procedures, vars, closedTerm);
			}
			m_Term2Predicates.put(term, predicate);
			assert predicate != null;
			return predicate;
		}
		
		private IPredicate getEquivalentPredicate(Term term, Set<BoogieVar> vars, Set<String> procs,
				ArrayList<IPredicate> impliedInterpolants, ArrayList<IPredicate> expliedInterpolants) {
			Term closedTerm = SmtManager.computeClosedFormula(term, vars, m_SmtManager.getScript());
			for (Term interpolantTerm : m_Term2Predicates.keySet()) {
				IPredicate interpolant = m_Term2Predicates.get(interpolantTerm);
				Term interpolantClosedTerm = interpolant.getClosedFormula();
//				String[] interpolantProcedures = 
//				if (interpolant.getProcedures().length == 0) {
//					interpolantProcedures = interpolant.getProcedures();
//				} else {
//					interpolantProcedure = interpolant.getProgramPoint().getProcedure();
//				}
				LBool implies;
//				if (interpolantProcedure == null || interpolantProcedure.equals(proc)) {
					implies = m_SmtManager.isCovered(closedTerm, interpolantClosedTerm); 
//				} else {
//					implies = LBool.UNKNOWN;
//				}
//				if (implies == LBool.UNSAT) {
					impliedInterpolants.add(interpolant);
//				}
				LBool explies;
//				if (interpolantProcedure == null || 
//						(proc != null && proc.equals(interpolantProcedure))) {
					explies = m_SmtManager.isCovered(interpolantClosedTerm, closedTerm);
//				} else {
//					explies = LBool.UNKNOWN;
//				}
//				if (explies == LBool.UNSAT) {
					expliedInterpolants.add(interpolant);
//				}
				if (implies == LBool.UNSAT && explies == LBool.UNSAT) {
					return interpolant;
				} 
			}
			return null;
		}
	}
	
	private boolean equivalentToFalse(Term term) {
		LBool sat = Util.checkSat(m_SmtManager.getScript(), term);
		switch (sat) {
		case UNSAT:
			return true;
		case SAT:
			return false;
		case UNKNOWN:
			s_Logger.warn(new DebugMessage("assuming that {0} is not equivalent to false", term));
			return false;
		default:
			throw new AssertionError();
		}
	}
	
	private boolean equivalentToTrue(Term term) {
		Term negation = m_SmtManager.getScript().term("not", term);
		LBool sat = Util.checkSat(m_SmtManager.getScript(), negation);
		switch (sat) {
		case UNSAT:
			return true;
		case SAT:
			return false;
		case UNKNOWN:
			s_Logger.warn(new DebugMessage("assuming that {0} is not equivalent to true", term));
			return false;
		default:
			throw new AssertionError();
		}
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