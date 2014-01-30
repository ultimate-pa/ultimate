package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Class that does the same as AnnotateAndAsserter but we do not assert the
 * SSA term but their conjuncts. Furthermore we store which conjunct 
 * corresponds to which original term.
 * @author Matthias Heizmann
 *
 */
public class AnnotateAndAsserterConjuncts extends AnnotateAndAsserter {
	
	Map<Term,Term> m_Annotated2Original = new HashMap<Term,Term>();
	protected final DefaultTransFormulas m_DefaultTransFormulas;

	public AnnotateAndAsserterConjuncts(SmtManager smtManager, 
			NestedFormulas<Term, Term> nestedSSA, DefaultTransFormulas defaultTransformulas) {
		super(smtManager, nestedSSA);
		m_DefaultTransFormulas = defaultTransformulas;
	}
	
	
	/**
	 * Take transition in single static assignment form (Term indexed), take
	 * its conjuncts, annotate each conjunct, assert the annotation, and
	 * store in m_Annotated2Original which indexed conjunct corresponds to
	 * which original conjunct.
	 * 
	 * @param name Prefix of this terms annotation (e.g., ssa_23, 
	 * LocVarAssigCall_42, precond, or any other of the static strings in the
	 * superclass).
	 * @param original Term that describes this transition as it occurs in the
	 * original TransFormula
	 * @param indexed Term that describes this transition in single static 
	 * assignment form.
	 * @return conjunction of annotated terms
	 */
	private Term annotateAndAssertConjuncts(String name, Term original,	Term indexed) {
		Term[] originalConjuncts = PartialQuantifierElimination.getConjuncts(original);
		Term[] indexedConjuncts = PartialQuantifierElimination.getConjuncts(indexed);
		assert originalConjuncts.length == indexedConjuncts.length : 
			"number of original and indexed conjuncts differ";
		Term[] annotatedConjuncts = new Term[originalConjuncts.length];
		for (int i=0; i<originalConjuncts.length; i++) {
			Term originalConjunct = originalConjuncts[i];
			Term indexedConjunct = indexedConjuncts[i];
			annotatedConjuncts[i] = annotateAndAssertTerm(indexedConjunct, name, i);
			m_Annotated2Original.put(annotatedConjuncts[i], originalConjunct);
		}
		return Util.and(m_Script, annotatedConjuncts);
	}
	
	
	/**
	 * Do the same as annotateAndAssertConjuncts() but do not split the term
	 * into conjuncts.
	 */
	private Term annotateAndAssertConjunction(String name, Term original, Term indexed) {
		Term annotated = super.annotateAndAssertTerm(indexed, name);
		m_Annotated2Original.put(annotated, original);
		return annotated;
	}
	
	@Override
	protected Term annotateAndAssertPrecondition() {
		String name = super.precondAnnotation();
		Term original = m_DefaultTransFormulas.getPrecondition().getFormula();
		Term indexed = m_SSA.getPrecondition();
		return annotateAndAssertConjuncts(name, original, indexed);
	}



	@Override
	protected Term annotateAndAssertPostcondition() {
		String name = super.postcondAnnotation();
		Term original = m_DefaultTransFormulas.getPostcondition().getFormula();
		Term indexed = m_Script.term("not", m_SSA.getPostcondition());
		return annotateAndAssertConjunction(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertNonCall(int position) {
		String name;
		if (m_Trace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			 name = internalAnnotation(position);
		}
		
		Term original = m_DefaultTransFormulas.getFormulaFromNonCallPos(position).getFormula();
		Term indexed = m_SSA.getFormulaFromNonCallPos(position);
		Term annotated = annotateAndAssertConjuncts(name, original, indexed);
		return annotated;
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
		String name = super.localVarAssignemntCallAnnotation(position);
		Term original = m_DefaultTransFormulas.getLocalVarAssignment(position).getFormula();
		Term indexed = m_SSA.getLocalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
		String name = super.globalVarAssignemntAnnotation(position);
		Term original = m_DefaultTransFormulas.getGlobalVarAssignment(position).getFormula();
		Term indexed = m_SSA.getGlobalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntCall(int position) {
		String name = super.oldVarAssignemntCallAnnotation(position);
		Term original = m_DefaultTransFormulas.getOldVarAssignment(position).getFormula();
		Term indexed = m_SSA.getOldVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertPendingContext(
			int positionOfPendingContext, int pendingContextCode) {
		String name = super.pendingContextAnnotation(pendingContextCode);
		Term original = m_DefaultTransFormulas.getPendingContext(positionOfPendingContext).getFormula();
		Term indexed = m_SSA.getPendingContext(positionOfPendingContext);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertLocalVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		String name = super.localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term original = m_DefaultTransFormulas.getLocalVarAssignment(positionOfPendingReturn).getFormula();
		Term indexed = m_SSA.getLocalVarAssignment(positionOfPendingReturn);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertOldVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		String name = super.oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term original = m_DefaultTransFormulas.getOldVarAssignment(positionOfPendingReturn).getFormula();
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
