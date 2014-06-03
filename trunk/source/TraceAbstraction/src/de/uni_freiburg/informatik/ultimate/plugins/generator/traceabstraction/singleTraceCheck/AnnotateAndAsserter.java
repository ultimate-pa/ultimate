package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * TODO: use quick check
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAsserter {
	
	protected static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		
		protected final Script m_Script;
		protected final SmtManager m_SmtManager;
		protected final NestedWord<CodeBlock> m_Trace;

		
		protected LBool m_Satisfiable;
		protected final NestedFormulas<Term, Term> m_SSA;
		protected ModifiableNestedFormulas<Term, Term> m_AnnotSSA;

		protected static final String SSA = "ssa_";
		protected static final String PRECOND = "precond";
		protected static final String POSTCOND = "postcond";
		protected static final String RETURN = "_return";
		protected static final String LOCVARASSIGN_CALL = "_LocVarAssigCall";
		protected static final String GLOBVARASSIGN_CALL = "_GlobVarAssigCall";
		protected static final String OLDVARASSIGN_CALL = "_OldVarAssigCall";
		protected static final String PENDINGCONTEXT = "_PendingContext";
		protected static final String LOCVARASSIGN_PENDINGCONTEXT = "_LocVarAssignPendingContext";
		protected static final String OLDVARASSIGN_PENDINGCONTEXT = "_OldVarAssignPendingContext";
		

		public AnnotateAndAsserter(SmtManager smtManager,
				NestedFormulas<Term, Term> nestedSSA) {
			m_SmtManager = smtManager;
			m_Script = smtManager.getScript();
			m_Trace = nestedSSA.getTrace();
			m_SSA = nestedSSA;
		}
			

		public void buildAnnotatedSsaAndAssertTerms() {
			if (m_AnnotSSA != null) {
				throw new AssertionError("already build");
			}
			assert m_Satisfiable == null;
			
			m_AnnotSSA = new ModifiableNestedFormulas<Term, Term>(m_Trace, new TreeMap<Integer, Term>());
			
			m_AnnotSSA.setPrecondition(annotateAndAssertPrecondition());
			m_AnnotSSA.setPostcondition(annotateAndAssertPostcondition());
			
			Collection<Integer> callPositions = new ArrayList<Integer>();
			Collection<Integer> pendingReturnPositions = new ArrayList<Integer>();
			for (int i=0; i<m_Trace.length(); i++) {
				if (m_Trace.isCallPosition(i)) {
					callPositions.add(i);
					m_AnnotSSA.setGlobalVarAssignmentAtPos(i, annotateAndAssertGlobalVarAssignemntCall(i));
					m_AnnotSSA.setLocalVarAssignmentAtPos(i, annotateAndAssertLocalVarAssignemntCall(i));
					m_AnnotSSA.setOldVarAssignmentAtPos(i, annotateAndAssertOldVarAssignemntCall(i));
				} else  {
					if (m_Trace.isReturnPosition(i) && m_Trace.isPendingReturn(i)) {
						pendingReturnPositions.add(i);
					}
					m_AnnotSSA.setFormulaAtNonCallPos(i, annotateAndAssertNonCall(i));
				}
			}
			
			assert callPositions.containsAll(m_Trace.getCallPositions());
			assert m_Trace.getCallPositions().containsAll(callPositions);
			

			// number that the pending context. The first pending context has
			// number -1, the second -2, ...
			int pendingContextCode = -1 - m_SSA.getTrace().getPendingReturns().size();
			for (Integer positionOfPendingReturn : m_SSA.getTrace().getPendingReturns().keySet()) {
				assert m_Trace.isPendingReturn(positionOfPendingReturn);
				{
					Term annotated = annotateAndAssertPendingContext(
							positionOfPendingReturn, pendingContextCode);
					m_AnnotSSA.setPendingContext(positionOfPendingReturn, annotated);
				}
				{
					Term annotated = annotateAndAssertLocalVarAssignemntPendingContext(
							positionOfPendingReturn, pendingContextCode);
					m_AnnotSSA.setLocalVarAssignmentAtPos(positionOfPendingReturn, annotated);
				}
				{
					Term annotated = annotateAndAssertOldVarAssignemntPendingContext(
							positionOfPendingReturn, pendingContextCode);
					m_AnnotSSA.setOldVarAssignmentAtPos(positionOfPendingReturn, annotated);
				}
				pendingContextCode++;
			}
			
			m_Satisfiable = m_SmtManager.getScript().checkSat();
			s_Logger.info("Conjunction of SSA is " + m_Satisfiable);
		}
		
		protected Term annotateAndAssertPrecondition() {
			String name = precondAnnotation();
			Term annotated = annotateAndAssertTerm(m_SSA.getPrecondition(),name);
			return annotated;
		}
		
		protected String precondAnnotation() {
			return SSA + PRECOND;
		}
		
		protected Term annotateAndAssertPostcondition() {
			String name = postcondAnnotation();
			Term negatedPostcondition = m_Script.term("not", m_SSA.getPostcondition());
			Term annotated = annotateAndAssertTerm(negatedPostcondition,name);
			return annotated;
		}
		
		protected String postcondAnnotation() {
			return SSA + POSTCOND;
		}
		
		protected Term annotateAndAssertNonCall(int position) {
			String name;
			if (m_Trace.isReturnPosition(position)) {
				name = returnAnnotation(position);
			} else {
				 name = internalAnnotation(position);
			}
			Term original = m_SSA.getFormulaFromNonCallPos(position);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String internalAnnotation(int position) {
			return SSA + position;
		}
		
		protected String returnAnnotation(int position) {
			return SSA + position + RETURN;
		}
		
		protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
			String name = localVarAssignemntCallAnnotation(position);
			Term original = m_SSA.getLocalVarAssignment(position);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String localVarAssignemntCallAnnotation(int position) {
			return SSA + position + LOCVARASSIGN_CALL;
		}
		
		protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
			String name = globalVarAssignemntAnnotation(position);
			Term original = m_SSA.getGlobalVarAssignment(position);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String globalVarAssignemntAnnotation(int position) {
			return SSA + position + GLOBVARASSIGN_CALL;
		}
		
		protected Term annotateAndAssertOldVarAssignemntCall(int position) {
			String name = oldVarAssignemntCallAnnotation(position);
			Term original = m_SSA.getOldVarAssignment(position);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String oldVarAssignemntCallAnnotation(int position) {
			return SSA + position + OLDVARASSIGN_CALL;
		}
		
		protected Term annotateAndAssertPendingContext(
				int positionOfPendingContext, int pendingContextCode) {
			String name = pendingContextAnnotation(pendingContextCode);
			Term original = m_SSA.getPendingContext(positionOfPendingContext);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String pendingContextAnnotation(int pendingContextCode) {
			return SSA + pendingContextCode + PENDINGCONTEXT;
		}
		
		protected Term annotateAndAssertLocalVarAssignemntPendingContext(
				int positionOfPendingReturn, int pendingContextCode) {
			String name = localVarAssignemntPendingReturnAnnotation(pendingContextCode);
			Term original = m_SSA.getLocalVarAssignment(positionOfPendingReturn);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String localVarAssignemntPendingReturnAnnotation(int pendingContextCode) {
			return SSA + pendingContextCode + LOCVARASSIGN_PENDINGCONTEXT;
		}
		
		protected Term annotateAndAssertOldVarAssignemntPendingContext(
				int positionOfPendingReturn, int pendingContextCode) {
			String name = oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
			Term original = m_SSA.getOldVarAssignment(positionOfPendingReturn);
			Term annotated = annotateAndAssertTerm(original, name);
			return annotated;
		}
		
		protected String oldVarAssignemntPendingReturnAnnotation(int pendingContextCode) {
			return SSA + pendingContextCode + OLDVARASSIGN_PENDINGCONTEXT;
		}
		
		
		
		protected Term annotateAndAssertTerm(Term term, String name) {
			assert term.getFreeVars().length == 0 : "Term has free vars";
			Annotation annot = new Annotation(":named", name);
			Term annotTerm = m_Script.annotate(term, annot);
			m_SmtManager.assertTerm(annotTerm);
			Term constantRepresentingAnnotatedTerm = m_Script.term(name);
			return constantRepresentingAnnotatedTerm;
		}
		
		

		public LBool isInputSatisfiable() {
			return m_Satisfiable;
		}
		
	
		
		
		/**
		 * Return a ParallelComposition-free trace of a trace.
		 * While using large block encoding this sequence is not unique.
		 * @param smtManager <ul>
		 * <li> If smtManager is null some branch of a ParallelComposition is taken.
		 * <li> If smtManager is not null, the smtManger has to be a state where a
		 * valuation of this traces branch indicators is available. Then some branch
		 * for which the branch indicator evaluates to true is taken.
		 */
		public static List<CodeBlock> constructFailureTrace(
				Word<CodeBlock> word, SmtManager smtManager) {
			List<CodeBlock> failurePath = new ArrayList<CodeBlock>();
			for (int i=0; i<word.length(); i++) {
				CodeBlock codeBlock = word.getSymbol(i);
				addToFailureTrace(codeBlock, i , failurePath, smtManager);
			}
			return failurePath;
		}
		
		/**
		 * Recursive method used by getFailurePath
		 */
		private static void addToFailureTrace(CodeBlock codeBlock, int pos, 
							List<CodeBlock> failureTrace, SmtManager smtManager) {
			if (codeBlock instanceof Call) {
				failureTrace.add(codeBlock);
			} else if (codeBlock instanceof Return) {
				failureTrace.add(codeBlock);
			} else if (codeBlock instanceof Summary) {
				failureTrace.add(codeBlock);
			} else if (codeBlock instanceof StatementSequence) {
				failureTrace.add(codeBlock);
			} else if (codeBlock instanceof SequentialComposition) {
				SequentialComposition seqComp = (SequentialComposition) codeBlock;
				for (CodeBlock elem : seqComp.getCodeBlocks()) {
					addToFailureTrace(elem, pos, failureTrace, smtManager);
				}
			} else if (codeBlock instanceof ParallelComposition) {
				ParallelComposition parComp = (ParallelComposition) codeBlock;
				
				Set<TermVariable> branchIndicators = parComp.getBranchIndicator2CodeBlock().keySet();
				
				TermVariable taken = null;
				
				if (smtManager == null) {
					// take some branch
					taken = branchIndicators.iterator().next();
				}
				else {
					// take some branch for which the branch indicator evaluates to
					// true
					for (TermVariable tv : branchIndicators) {
						String constantName = tv.getName()+"_"+pos;
						Term constant = smtManager.getScript().term(constantName);
						Term[] terms = { constant };
						Map<Term, Term> valuation = smtManager.getScript().getValue(terms);
						Term value = valuation.get(constant);
						if (value == smtManager.getScript().term("true")) {
							taken = tv;
						}
					}
				}
				assert (taken != null);
				CodeBlock cb = parComp.getBranchIndicator2CodeBlock().get(taken); 
				addToFailureTrace(cb, pos, failureTrace, smtManager);
			} else {
				throw new IllegalArgumentException("unkown code block");
			}
		}


		public NestedFormulas<Term, Term> getAnnotatedSsa() {
			return m_AnnotSSA;
		}
		


}
