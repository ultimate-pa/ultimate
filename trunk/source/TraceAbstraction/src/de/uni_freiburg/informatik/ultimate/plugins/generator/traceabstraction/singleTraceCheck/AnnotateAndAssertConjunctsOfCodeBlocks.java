package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Class that does the same as AnnotateAndAsserter but we do not assert the
 * SSA term but their conjuncts. Furthermore we store which conjunct 
 * corresponds to which original term.
 * @author Matthias Heizmann
 *
 */
public class AnnotateAndAssertConjunctsOfCodeBlocks extends AnnotateAndAssertCodeBlocks {
	
	protected final DefaultTransFormulas m_DefaultTransFormulas;
	private final Map<Term,Term> m_Annotated2Original = new HashMap<Term,Term>();
	private final SplitEqualityMapping m_SplitEqualityMapping = new SplitEqualityMapping();
	
	private final static boolean m_SplitEqualities = false;

	public AnnotateAndAssertConjunctsOfCodeBlocks(SmtManager smtManager, 
			NestedFormulas<Term, Term> nestedSSA, DefaultTransFormulas defaultTransformulas, Logger logger) {
		super(smtManager, nestedSSA,logger);
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
		Term[] originalConjuncts = SmtUtils.getConjuncts(original);
		Term[] indexedConjuncts = SmtUtils.getConjuncts(indexed);
		assert originalConjuncts.length == indexedConjuncts.length : 
			"number of original and indexed conjuncts differ";
		
		if (m_SplitEqualities) {
			List<Term> originalConjunctsEqualitiesTransformed = new LinkedList<Term>();
			List<Term> indexedConjunctsEqualitiesTransformed = new LinkedList<Term>();
			
			for (int i = 0; i<originalConjuncts.length; i++) {
				Term[] conjunctInequalities = transformEqualityToInequalities(originalConjuncts[i]);
				Term[] indexedConjunctInequalities = transformEqualityToInequalities(indexedConjuncts[i]);
				assert conjunctInequalities.length == indexedConjunctInequalities.length : 
					"number of original and indexed conjuncts after transforming equalities to inequalities differ";

				originalConjunctsEqualitiesTransformed.add(conjunctInequalities[0]);
				indexedConjunctsEqualitiesTransformed.add(indexedConjunctInequalities[0]);
				if (conjunctInequalities.length == 2) {
					originalConjunctsEqualitiesTransformed.add(conjunctInequalities[1]);
					indexedConjunctsEqualitiesTransformed.add(indexedConjunctInequalities[1]);
				}
			}
			originalConjuncts = originalConjunctsEqualitiesTransformed.toArray(new Term[originalConjunctsEqualitiesTransformed.size()]);
			indexedConjuncts = indexedConjunctsEqualitiesTransformed.toArray(new Term[indexedConjunctsEqualitiesTransformed.size()]);
			
		}
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
	 * Returns a representation of Term as BinaryNumericRelation if term is
	 * a binary equality whose parameters have a Sort that is numeric.
	 */
	private BinaryNumericRelation convertToBinaryNumericEquality(Term term) {
		BinaryNumericRelation result;
		try {
			result = new BinaryNumericRelation(term);
		} catch (NoRelationOfThisKindException e) {
			return null;
		}
		if (result.getRelationSymbol() == RelationSymbol.EQ) {
			return result;
		} else {
			return null;
		}
	}


	private Term[] transformEqualityToInequalities(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm ap = (ApplicationTerm) term;
			if (ap.getFunction().getName() == "=") {
				Term[] params = ap.getParameters();
				assert params.length == 2 : "only for binary \"=\" implemented";
				if (params[0].getSort().isNumericSort() || 
						params[1].getSort().isNumericSort()) {
					Term firstConjunct = m_Script.term("<=", params[0], params[1]);
					Term secondConjunct = m_Script.term("<=", params[1], params[0]);
					return new Term[]{firstConjunct, secondConjunct};
				}
			}
		}
		return new Term[]{term};
	}


	/**
	 * Returns a mapping from named terms (that were asserted) to the conjuncts
	 * to which these named terms correspond.
	 */
	public Map<Term, Term> getAnnotated2Original() {
		return m_Annotated2Original;
	}
	
	
	public SplitEqualityMapping getSplitEqualityMapping() {
		return m_SplitEqualityMapping;
	}


	/**
	 * Provides two information for each equality a=b that was split into
	 * two inequalities a>=b, a<=b.
	 * For the equality a=b, the map m_Inequality2CorrespondingInequality 
	 * contains the following two pairs:
	 * (a>=b, a<=b) (a<=b, a>=b)
	 * For the equality a=b, the map m_Inequality2OriginalEquality contains 
	 * the following two pairs:
	 * (a>=b, a=b) (a<=b, a=b)
	 *
	 */
	public class SplitEqualityMapping {
		private final Map<Term, Term> m_Inequality2CorrespondingInequality = new HashMap<>();
		private final Map<Term, Term> m_Inequality2OriginalEquality = new HashMap<>();
		
		void add(Term firstInequality, Term secondInequality, Term orginalEquality) {
			m_Inequality2CorrespondingInequality.put(firstInequality, secondInequality);
			m_Inequality2CorrespondingInequality.put(secondInequality, firstInequality);
			m_Inequality2OriginalEquality.put(firstInequality, orginalEquality);
			m_Inequality2OriginalEquality.put(secondInequality, orginalEquality);
		}

		public Map<Term, Term> getInequality2CorrespondingInequality() {
			return Collections.unmodifiableMap(m_Inequality2CorrespondingInequality);
		}

		public Map<Term, Term> getInequality2OriginalEquality() {
			return Collections.unmodifiableMap(m_Inequality2OriginalEquality);
		}
	}
	
}
