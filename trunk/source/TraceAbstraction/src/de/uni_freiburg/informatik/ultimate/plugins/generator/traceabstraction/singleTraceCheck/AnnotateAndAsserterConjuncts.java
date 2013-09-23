package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.DestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class AnnotateAndAsserterConjuncts extends AnnotateAndAsserter {
	
	Map<Term,Term> m_Annotated2Original = new HashMap<Term,Term>();

	public AnnotateAndAsserterConjuncts(SmtManager smtManager, NestedSsa nestedSSA) {
		super(smtManager, nestedSSA);
	}
	
	
	/**
	 * @param name
	 * @param original
	 * @param indexed
	 * @return
	 */
	private Term annotateAndAssertConjuncts(String name, Term original,	Term indexed) {
		Term[] originalConjuncts = DestructiveEqualityResolution.getConjuncts(original);
		Term[] indexedConjuncts = DestructiveEqualityResolution.getConjuncts(indexed);
		assert originalConjuncts.length == indexedConjuncts.length;
		Term[] annotatedConjuncts = new Term[originalConjuncts.length];
		for (int i=0; i<originalConjuncts.length; i++) {
			Term originalConjunct = originalConjuncts[i];
			Term indexedConjunct = indexedConjuncts[i];
			annotatedConjuncts[i] = annotateAndAssertTerm(indexedConjunct, name, i);
			m_Annotated2Original.put(annotatedConjuncts[i], originalConjunct);
		}
		return Util.and(m_Script, annotatedConjuncts);
	}
	
	@Override
	protected Term annotateAndAssertPrecondition() {
		String name = super.precondAnnotation();
		Term original = m_SSA.getTransFormulas().getPrecondition().getFormula();
		Term indexed = m_SSA.getPrecondition();
		return annotateAndAssertConjuncts(name, original, indexed);
	}



	@Override
	protected Term annotateAndAssertPostcondition() {
		String name = super.postcondAnnotation();
		Term original = m_SSA.getTransFormulas().getPostcondition().getFormula();
		Term indexed = m_Script.term("not", m_SSA.getPostcondition());
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertNonCall(int position) {
		String name;
		if (m_Trace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			 name = internalAnnotation(position);
		}
		
		Term original = m_SSA.getTransFormulas().getFormulaFromNonCallPos(position).getFormula();
		Term indexed = m_SSA.getFormulaFromNonCallPos(position);
		Term annotated = annotateAndAssertConjuncts(name, original, indexed);
		return annotated;
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
		String name = super.localVarAssignemntCallAnnotation(position);
		Term original = m_SSA.getTransFormulas().getLocalVarAssignment(position).getFormula();
		Term indexed = m_SSA.getLocalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
		String name = super.globalVarAssignemntAnnotation(position);
		Term original = m_SSA.getTransFormulas().getGlobalVarAssignment(position).getFormula();
		Term indexed = m_SSA.getGlobalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntCall(int position) {
		String name = super.oldVarAssignemntCallAnnotation(position);
		Term original = m_SSA.getTransFormulas().getOldVarAssignment(position).getFormula();
		Term indexed = m_SSA.getOldVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertPendingContext(
			int positionOfPendingContext, int pendingContextCode) {
		String name = super.pendingContextAnnotation(pendingContextCode);
		Term original = m_SSA.getTransFormulas().getPendingContexts().get(positionOfPendingContext).getFormula();
		Term indexed = m_SSA.getPendingContexts().get(positionOfPendingContext);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertLocalVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		String name = super.localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term original = m_SSA.getTransFormulas().getLocalVarAssignment(positionOfPendingReturn).getFormula();
		Term indexed = m_SSA.getLocalVarAssignment(positionOfPendingReturn);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertOldVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		String name = super.oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term original = m_SSA.getTransFormulas().getOldVarAssignment(positionOfPendingReturn).getFormula();
		Term indexed = m_SSA.getOldVarAssignment(positionOfPendingReturn);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	protected Term annotateAndAssertTerm(Term term, String name, int conjunct) {
		name += "_conjunct" + conjunct;
		return super.annotateAndAssertTerm(term, name);
	}


	/**
	 * Returns a mapping from named terms (that were asserted) to the conjuncts
	 * to which these named terms correspond.
	 */
	public Map<Term, Term> getAnnotated2Original() {
		return m_Annotated2Original;
	}
	
}
