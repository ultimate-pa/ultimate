package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * TODO: use quick check
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAsserter {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		
		protected final Script m_Script;
		protected final SmtManager m_SmtManager;
		protected final NestedWord<CodeBlock> m_Trace;
		
		protected final LBool m_Satisfiable;
		protected final NestedSsa m_AnnotSSA;

		public AnnotateAndAsserter(SmtManager smtManager, NestedSsa nestedSSA, Word<CodeBlock> trace) {
			m_SmtManager = smtManager;
			m_Script = smtManager.getScript();
			if (trace instanceof NestedWord) {
				m_Trace = (NestedWord<CodeBlock>) trace;
			} else {
				m_Trace = new NestedWord<CodeBlock>(trace);
			}
			m_AnnotSSA = buildAnnotatedSsaAndAssertTerms(nestedSSA);

			m_Satisfiable = m_SmtManager.getScript().checkSat();
			s_Logger.info("Conjunction of SSA is " + m_Satisfiable);
			
			}
			

		protected NestedSsa buildAnnotatedSsaAndAssertTerms(NestedSsa nestedSsa) {
			Term[] terms = nestedSsa.getTerms();
			Term[] annotatedTerms = new Term[nestedSsa.getTerms().length];
			for (int i=0; i<terms.length; i++) {
				Term term = terms[i];
				assert term.getFreeVars().length == 0 : "Term has free vars";
				String name;
				if (m_Trace.isCallPosition(i)) {
					name = "ssa_" + i + "_callglobVarAssign";
				} else if (m_Trace.isReturnPosition(i)) {
					name = "ssa_" + i + "_return";
				} else {
					name = "ssa_"+i;
				}
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = m_Script.annotate(term, annot);
				m_SmtManager.assertTerm(annotTerm);
				Term constantRepresentingAnnotatedTerm = m_Script.term(name);
				annotatedTerms[i] = constantRepresentingAnnotatedTerm;
			}
			
			Map<Integer, Term> localVarAssignmentAtCall = nestedSsa.getLocalVarAssignmentAtCall();
			HashMap<Integer, Term> annotatedLocalVarAssignmentAtCall = new HashMap<Integer,Term>();
			for (Integer position : localVarAssignmentAtCall.keySet()) {
				// FIXME separate map pending returns
				if (m_Trace.isPendingReturn(position)) {
					continue;
				}
				assert m_Trace.isCallPosition(position);
				Term term = localVarAssignmentAtCall.get(position);
				assert term.getFreeVars().length == 0 : "Term has free vars";
				String name = "ssa_" + position + "_calllocVarAssign";
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = m_Script.annotate(term, annot);
				m_SmtManager.assertTerm(annotTerm);
				Term constantRepresentingAnnotatedTerm = m_Script.term(name);
				annotatedLocalVarAssignmentAtCall.put(position, constantRepresentingAnnotatedTerm);			
			}
			
			Map<Integer, Term> globalOldVarAssignmentAtCall = nestedSsa.getGlobalOldVarAssignmentAtCall();
			HashMap<Integer, Term> annotatedGlobalOldVarAssignmentAtCall = new HashMap<Integer,Term>();
			for (Integer position : globalOldVarAssignmentAtCall.keySet()) {
				// FIXME separate map pending returns
				if (m_Trace.isPendingReturn(position)) {
					continue;
				}
				assert m_Trace.isCallPosition(position);
				Term term = globalOldVarAssignmentAtCall.get(position);
				assert term.getFreeVars().length == 0 : "Term has free vars";
				String name = "ssa_" + position + "_calloldVarAssign";
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = m_Script.annotate(term, annot);
				m_SmtManager.assertTerm(annotTerm);
				Term constantRepresentingAnnotatedTerm = m_Script.term(name);
				annotatedGlobalOldVarAssignmentAtCall.put(position, constantRepresentingAnnotatedTerm);			
			}
			
			SortedMap<Integer, Term> pendingContexts = nestedSsa.getPendingContexts();
			SortedMap<Integer, Term> annotatedPendingContexts = new TreeMap<Integer,Term>();
			int pendingReturnCode = -1 - pendingContexts.size();
			for (Integer position : pendingContexts.keySet()) {
				assert m_Trace.isPendingReturn(position);
				{
					Term term = pendingContexts.get(position);
					assert term.getFreeVars().length == 0 : "Term has free vars";
					String name = "ssa_pendingContext"+pendingReturnCode;
					Annotation annot = new Annotation(":named", name);
					Term annotTerm = m_Script.annotate(term, annot);
					m_SmtManager.assertTerm(annotTerm);
					Term constantRepresentingAnnotatedTerm = m_Script.term(name);
					annotatedPendingContexts.put(position, constantRepresentingAnnotatedTerm);
				}
				{
					Term term = localVarAssignmentAtCall.get(position);
					assert term.getFreeVars().length == 0 : "Term has free vars";
					String name = "ssa_" + position + "pendingCalllocalVarAssig";
					Annotation annot = new Annotation(":named", name);
					Term annotTerm = m_Script.annotate(term, annot);
					m_SmtManager.assertTerm(annotTerm);
					Term constantRepresentingAnnotatedTerm = m_Script.term(name);
					annotatedLocalVarAssignmentAtCall.put(position, constantRepresentingAnnotatedTerm);
				}
				{
					Term term = globalOldVarAssignmentAtCall.get(position);
					assert term.getFreeVars().length == 0 : "Term has free vars";
					String name = "ssa_" + position + "pendingCalloldVarAssign";
					Annotation annot = new Annotation(":named", name);
					Term annotTerm = m_Script.annotate(term, annot);
					m_SmtManager.assertTerm(annotTerm);
					Term constantRepresentingAnnotatedTerm = m_Script.term(name);
					annotatedGlobalOldVarAssignmentAtCall.put(position, constantRepresentingAnnotatedTerm);
				}

				pendingReturnCode++;
			}

			
			
			Map<Term, BoogieVar> constants2BoogieVar = nestedSsa.getConstants2BoogieVar();

			
			NestedSsa annotatedNestedSSA = new NestedSsa(
					m_Trace,
					annotatedTerms, annotatedLocalVarAssignmentAtCall, annotatedGlobalOldVarAssignmentAtCall, 
					annotatedPendingContexts,
					constants2BoogieVar);
			
			{
				Term term = nestedSsa.getPrecondition();
				assert term.getFreeVars().length == 0 : "Term has free vars";
				String name = "ssa_precond";
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = m_Script.annotate(term, annot);
				m_SmtManager.assertTerm(annotTerm);
				Term constantRepresentingAnnotatedTerm = m_Script.term(name);
				annotatedNestedSSA.setPrecondition(constantRepresentingAnnotatedTerm);
			}
			
			{
				Term term = nestedSsa.getPostcondition();
				assert term.getFreeVars().length == 0 : "Term has free vars";
				term = m_Script.term("not",term);
				String name = "ssa_negPostcond";
				Annotation annot = new Annotation(":named", name);
				Term annotTerm = m_Script.annotate(term, annot);
				m_SmtManager.assertTerm(annotTerm);
				Term constantRepresentingAnnotatedTerm = m_Script.term(name);
				annotatedNestedSSA.setPostcondition(constantRepresentingAnnotatedTerm);
			}
			
			
			
			return annotatedNestedSSA;
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


		public NestedSsa getAnnotSSA() {
			return m_AnnotSSA;
		}

}
