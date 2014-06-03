package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
/**
 * TODO: Documentation!
 * @author Betim Musa
 *
 */
public class AnnotateAndAsserterWithStmtOrderPrioritization extends AnnotateAndAsserterConjuncts {

	public AnnotateAndAsserterWithStmtOrderPrioritization(
			SmtManager smtManager, NestedFormulas<Term, Term> nestedSSA,
			DefaultTransFormulas defaultTransformula) {
		super(smtManager, nestedSSA, defaultTransformula);
		// TODO Auto-generated constructor stub
	}

	private Set<CodeBlock> getStatementsWithoutLoop(NestedWord<CodeBlock> trace) {
		
		List<ProgramPoint> pps = TraceCheckerUtils.getSequenceOfProgramPoints(trace);
		Set<CodeBlock> stmtsBeforeLoop = new HashSet<CodeBlock>();
		List<CodeBlock> stmtsAfterLoop = new ArrayList<CodeBlock>();
		boolean loopEntryFound = false;
		boolean loopExitFound = false;
		for (int i = 0; i <= trace.length() / 2; i++) {
			if (!loopEntryFound) {
				if (pps.get(i).getPosition().endsWith("loopEntry'")) {
					loopEntryFound = true;
				} else {
					stmtsBeforeLoop.add(trace.getSymbol(i));
				}
			}
			if (!loopExitFound) {
				int j = trace.length() - (i+1);
				if (pps.get(j).getPosition().endsWith("loopEntry'")) {
					if (j == i) {
						stmtsAfterLoop.add(trace.getSymbol(j));
					}
					loopExitFound = true;
				} else {
					stmtsAfterLoop.add(trace.getSymbol(j));
				}
			}
			if (loopEntryFound && loopExitFound) {
				break;
			}
		}
		stmtsBeforeLoop.addAll(stmtsAfterLoop);
//		return NestedWord.nestedWord(new Word<CodeBlock>(stmtsBeforeLoop.toArray(new CodeBlock[stmtsBeforeLoop.size()])));
		return new HashSet<CodeBlock>(stmtsBeforeLoop);
	}

	@Override
	public void buildAnnotatedSsaAndAssertTerms() {
		Set<CodeBlock> stmtsWithoutLoop = getStatementsWithoutLoop(m_Trace);
		
		m_AnnotSSA = new ModifiableNestedFormulas<Term, Term>(m_Trace, new TreeMap<Integer, Term>());
		
		m_AnnotSSA.setPrecondition(annotateAndAssertPrecondition());
		m_AnnotSSA.setPostcondition(annotateAndAssertPostcondition());
		buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(m_Trace, stmtsWithoutLoop, true);
	}
	
	/**
	 * TODO: Documentation
	 * @param trace
	 * @param stmtsWithOutLoop
	 * @param tryWithOutLoop
	 */
	private void buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(NestedWord<CodeBlock> trace, 
			Set<CodeBlock> stmtsWithOutLoop,
			boolean tryWithOutLoop) {
		
		Collection<Integer> callPositions = new ArrayList<Integer>();
		Collection<Integer> pendingReturnPositions = new ArrayList<Integer>();
		for (int i=0; i< trace.length(); i++) {
			if (tryWithOutLoop && !stmtsWithOutLoop.contains(trace.getSymbol(i))) {
				continue;
			} else if (!tryWithOutLoop && stmtsWithOutLoop.contains(trace.getSymbol(i))) {
				continue;
			}
			if (trace.isCallPosition(i)) {
				callPositions.add(i);
				m_AnnotSSA.setGlobalVarAssignmentAtPos(i, annotateAndAssertGlobalVarAssignemntCall(i));
				m_AnnotSSA.setLocalVarAssignmentAtPos(i, annotateAndAssertLocalVarAssignemntCall(i));
				m_AnnotSSA.setOldVarAssignmentAtPos(i, annotateAndAssertOldVarAssignemntCall(i));
			} else  {
				if (trace.isReturnPosition(i) && trace.isPendingReturn(i)) {
					pendingReturnPositions.add(i);
				}
				m_AnnotSSA.setFormulaAtNonCallPos(i, annotateAndAssertNonCall(i));
			}
		}
		
		// TODO: Do we have to remove these assertions
		assert callPositions.containsAll(trace.getCallPositions());
		assert trace.getCallPositions().containsAll(callPositions);

		// number that the pending context. The first pending context has
		// number -1, the second -2, ...
		int pendingContextCode = -1 - m_SSA.getTrace().getPendingReturns().size();
		for (Integer positionOfPendingReturn : m_SSA.getTrace().getPendingReturns().keySet()) {
			assert trace.isPendingReturn(positionOfPendingReturn);
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
		if (tryWithOutLoop && m_Satisfiable != LBool.UNSAT) {
			buildAnnotatedSsaAndAssertTermsWithPriorizedOrder(trace, stmtsWithOutLoop, false);
		}
		s_Logger.info("Conjunction of SSA is " + m_Satisfiable);
	}
	
}
