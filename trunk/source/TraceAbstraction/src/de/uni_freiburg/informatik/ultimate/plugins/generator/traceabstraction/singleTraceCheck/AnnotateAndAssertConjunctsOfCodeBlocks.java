/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Class that does the same as AnnotateAndAsserter but we do not assert the
 * SSA term but their conjuncts. Furthermore we store which conjunct 
 * corresponds to which original term.
 * @author Matthias Heizmann
 *
 */
public class AnnotateAndAssertConjunctsOfCodeBlocks extends AnnotateAndAssertCodeBlocks {
	
	protected final NestedFormulas<UnmodifiableTransFormula, IPredicate> mNestedFormulas;
	private final Map<Term,Term> mAnnotated2Original = new HashMap<Term,Term>();
	private final SplitEqualityMapping mSplitEqualityMapping = new SplitEqualityMapping();
	private final SmtManager mSmtManagerPredicates;
	
	private final static boolean mSplitEqualities = true;

	public AnnotateAndAssertConjunctsOfCodeBlocks(SmtManager smtManager, 
			NestedFormulas<Term, Term> nestedSSA, 
			NestedFormulas<UnmodifiableTransFormula, IPredicate> nestedFormulas, ILogger logger,
			SmtManager smtManagerPredicates) {
		super(smtManager, nestedSSA,logger);
		mNestedFormulas = nestedFormulas;
		mSmtManagerPredicates = smtManagerPredicates;
	}
	
	
	/**
	 * Take transition in single static assignment form (Term indexed), take
	 * its conjuncts, annotate each conjunct, assert the annotation, and
	 * store in mAnnotated2Original which indexed conjunct corresponds to
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
		final Term[] originalConjuncts = SmtUtils.getConjuncts(original);
		final Term[] indexedConjuncts = SmtUtils.getConjuncts(indexed);
		assert originalConjuncts.length == indexedConjuncts.length : 
			"number of original and indexed conjuncts differ";
		
		final List<Term> annotatedConjuncts = new LinkedList<Term>();
		int annotatedTermsCounter = 0;
		
		for (int i=0; i<originalConjuncts.length; i++) {
			final Term originalConjunct = originalConjuncts[i];
			final Term indexedConjunct = indexedConjuncts[i];
			if (mSplitEqualities) {
				final BinaryNumericRelation bnr_originalConjunct = convertToBinaryNumericEquality(originalConjunct);
				if (bnr_originalConjunct != null) {
					final BinaryNumericRelation bnr_indexedConjunct = convertToBinaryNumericEquality(indexedConjunct);
					final Term[] conjunctAsInequalities_indexed =  transformEqualityToInequalities(bnr_indexedConjunct, mSmtManager.getScript());
					final Term[] conjunctAsInequalities_original = transformEqualityToInequalities(bnr_originalConjunct, mSmtManagerPredicates.getScript());
					// Annotate and store the first inequality
					annotatedConjuncts.add(annotateAndAssertTerm(conjunctAsInequalities_indexed[0], name, annotatedTermsCounter));
					// Caution! The map mAnnotated2Original is only correct, if BinaryNumericRelation splits the original_conjunct and the indexed_conjunct, such
					// that the getLhs() and getRhs() methods return the same terms.
					mAnnotated2Original.put(annotatedConjuncts.get(annotatedTermsCounter), conjunctAsInequalities_original[0]);
					// Annotate and store the second inequality
					annotatedConjuncts.add(annotateAndAssertTerm(conjunctAsInequalities_indexed[1], name, annotatedTermsCounter + 1));
					mAnnotated2Original.put(annotatedConjuncts.get(annotatedTermsCounter + 1), conjunctAsInequalities_original[1]);

					// Put the first annotated inequality and the second annotated inequality into mSplitEqualityMapping
					mSplitEqualityMapping.add(annotatedConjuncts.get(annotatedTermsCounter), annotatedConjuncts.get(annotatedTermsCounter+1), originalConjunct);
					annotatedTermsCounter = annotatedTermsCounter + 2;
				} else {
					annotatedConjuncts.add(annotateAndAssertTerm(indexedConjunct, name, annotatedTermsCounter));
					mAnnotated2Original.put(annotatedConjuncts.get(annotatedTermsCounter), originalConjunct);
					annotatedTermsCounter = annotatedTermsCounter + 1;
				}
			} else {
				annotatedConjuncts.add(annotateAndAssertTerm(indexedConjunct, name, annotatedTermsCounter));
				mAnnotated2Original.put(annotatedConjuncts.get(annotatedTermsCounter), originalConjunct);
				annotatedTermsCounter = annotatedTermsCounter + 1;
			}
		}
		return Util.and(mScript, annotatedConjuncts.toArray(new Term[annotatedConjuncts.size()]));
	}
	
	
	/**
	 * Do the same as annotateAndAssertConjuncts() but do not split the term
	 * into conjuncts.
	 */
	private Term annotateAndAssertConjunction(String name, Term original, Term indexed) {
		final Term annotated = super.annotateAndAssertTerm(indexed, name);
		mAnnotated2Original.put(annotated, original);
		return annotated;
	}
	
	@Override
	protected Term annotateAndAssertPrecondition() {
		final String name = super.precondAnnotation();
		final Term original = mNestedFormulas.getPrecondition().getFormula();
		final Term indexed = mSSA.getPrecondition();
		return annotateAndAssertConjuncts(name, original, indexed);
	}



	@Override
	protected Term annotateAndAssertPostcondition() {
		final String name = super.postcondAnnotation();
		final Term original = mNestedFormulas.getPostcondition().getFormula();
		final Term indexed = mScript.term("not", mSSA.getPostcondition());
		return annotateAndAssertConjunction(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertNonCall(int position) {
		String name;
		if (mTrace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			 name = internalAnnotation(position);
		}
		
		final Term original = mNestedFormulas.getFormulaFromNonCallPos(position).getFormula();
		final Term indexed = mSSA.getFormulaFromNonCallPos(position);
		final Term annotated = annotateAndAssertConjuncts(name, original, indexed);
		return annotated;
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
		final String name = super.localVarAssignemntCallAnnotation(position);
		final Term original = mNestedFormulas.getLocalVarAssignment(position).getFormula();
		final Term indexed = mSSA.getLocalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
		final String name = super.globalVarAssignemntAnnotation(position);
		final Term original = mNestedFormulas.getGlobalVarAssignment(position).getFormula();
		final Term indexed = mSSA.getGlobalVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntCall(int position) {
		final String name = super.oldVarAssignemntCallAnnotation(position);
		final Term original = mNestedFormulas.getOldVarAssignment(position).getFormula();
		final Term indexed = mSSA.getOldVarAssignment(position);
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertPendingContext(
			int positionOfPendingContext, int pendingContextCode) {
		final String name = super.pendingContextAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getPendingContext(positionOfPendingContext).getFormula();
		final Term indexed = mSSA.getPendingContext(positionOfPendingContext);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertLocalVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		final String name = super.localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getLocalVarAssignment(positionOfPendingReturn).getFormula();
		final Term indexed = mSSA.getLocalVarAssignment(positionOfPendingReturn);
		return annotateAndAssertConjuncts(name, original, indexed);
	}


	@Override
	protected Term annotateAndAssertOldVarAssignemntPendingContext(
			int positionOfPendingReturn, int pendingContextCode) {
		final String name = super.oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getOldVarAssignment(positionOfPendingReturn).getFormula();
		final Term indexed = mSSA.getOldVarAssignment(positionOfPendingReturn);
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
		} catch (final NoRelationOfThisKindException e) {
			return null;
		}
		// we do not use this transformation if params have bitvector sort
		if (BitvectorUtils.isBitvectorSort(result.getRhs().getSort())) {
			return null;
		}
		if (result.getRelationSymbol() == RelationSymbol.EQ) {
			return result;
		} else {
			return null;
		}
	}


	private Term[] transformEqualityToInequalities(BinaryNumericRelation bnr, Script script) {
		final Term firstConjunct = script.term("<=", bnr.getLhs(), bnr.getRhs());
		final Term secondConjunct = script.term(">=", bnr.getLhs(), bnr.getRhs());
		return new Term[] {firstConjunct, secondConjunct};
	}


	/**
	 * Returns a mapping from named terms (that were asserted) to the conjuncts
	 * to which these named terms correspond.
	 */
	public Map<Term, Term> getAnnotated2Original() {
		return mAnnotated2Original;
	}
	
	
	public SplitEqualityMapping getSplitEqualityMapping() {
		return mSplitEqualityMapping;
	}


	/**
	 * Provides two information for each equality a=b that was split into
	 * two inequalities a>=b, a<=b.
	 * For the equality a=b, the map mInequality2CorrespondingInequality 
	 * contains the following two pairs:
	 * (a>=b, a<=b) (a<=b, a>=b)
	 * For the equality a=b, the map mInequality2OriginalEquality contains 
	 * the following two pairs:
	 * (a>=b, a=b) (a<=b, a=b)
	 *
	 */
	public class SplitEqualityMapping {
		private final Map<Term, Term> mInequality2CorrespondingInequality = new HashMap<>();
		private final Map<Term, Term> mInequality2OriginalEquality = new HashMap<>();
		
		void add(Term firstInequality, Term secondInequality, Term orginalEquality) {
			mInequality2CorrespondingInequality.put(firstInequality, secondInequality);
			mInequality2CorrespondingInequality.put(secondInequality, firstInequality);
			mInequality2OriginalEquality.put(firstInequality, orginalEquality);
			mInequality2OriginalEquality.put(secondInequality, orginalEquality);
		}

		public Map<Term, Term> getInequality2CorrespondingInequality() {
			return Collections.unmodifiableMap(mInequality2CorrespondingInequality);
		}

		public Map<Term, Term> getInequality2OriginalEquality() {
			return Collections.unmodifiableMap(mInequality2OriginalEquality);
		}
	}
	
}
