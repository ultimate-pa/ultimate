package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcSettings;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraintConjunction;

public class CongruenceClosureSmtUtils {
	public static <NODE extends IEqNodeIdentifier<NODE>> Term congruenceClosureToTerm(final Script script,
			final CongruenceClosure<NODE> pa, final Term literalDisequalities) {
		return SmtUtils.and(script, congruenceClosureToCube(script, pa, literalDisequalities));
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> List<Term> congruenceClosureToCube(final Script script,
			final CongruenceClosure<NODE> pa, final Term literalDisequalities) {
		if (pa.isInconsistent()) {
			return Collections.singletonList(script.term("false"));
		}

		final List<Term> elementEqualities = pa.getSupportingElementEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = pa.getElementDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());

		final List<Term> result = new ArrayList<>(elementEqualities.size() + elementDisequalities.size());
		result.addAll(elementEqualities);
		result.addAll(elementDisequalities);

		if (CcSettings.IMPLICIT_LITERAL_DISEQUALITIES) {
			result.add(literalDisequalities);
		}


		for (final Entry<NODE, SetConstraintConjunction<NODE>> en :
				pa.getLiteralSetConstraints().getConstraints().entrySet()) {
			result.add(literalSetConstraintToTerm(script, en.getValue()));
		}

		return result;
	}

	private static <NODE extends IEqNodeIdentifier<NODE>> Term literalSetConstraintToTerm(final Script script,
//			final Entry<NODE, Set<NODE>> en) {
			final SetConstraintConjunction<NODE> constraint) {
//		assert !en.getValue().isEmpty();
//		assert !en.getKey().isLiteral();

		final Set<Term> conjuncts = new HashSet<>();
		for (final Set<NODE> set : constraint.getElementSets()) {
			final Set<Term> disjuncts = new HashSet<>();
			for (final NODE node : set) {
				disjuncts.add(SmtUtils.binaryEquality(script,
						constraint.getConstrainedElement().getTerm(),
						node.getTerm()));
			}
			conjuncts.add(SmtUtils.or(script, disjuncts));
		}
		return SmtUtils.and(script, conjuncts);
//		final Set<Term> disjuncts = new HashSet<>();
//		for (final NODE lit : constraint.) {
//			disjuncts.add(SmtUtils.binaryEquality(script, en.getKey().getTerm(), lit.getTerm()));
//		}
//		return SmtUtils.or(script, disjuncts);
	}

	/**
	 *
	 * @param script
	 * @param literalTerms
	 * 			the set of all literals relevant in the current context (including theory literals)
	 * @return a set of (distinct l1 l2) terms where l1 and l2 are not both theory literals and not identical
	 */
	public static List<Term> createDisequalityTermsForNonTheoryLiterals(final Script script,
			final Set<Term> literalTerms) {
		final List<Term> nonTheoryLiteralDisequalities = new ArrayList<>();
		/*
		 * the theory knows that normal constants are different from each other, also terms of different sorts
		 *  --> don't add those disequalities
		 */
		final BiPredicate<Term, Term> pairSelector = (l1, l2) -> l1 != l2
				&& (!(l1 instanceof ConstantTerm) || !(l2 instanceof ConstantTerm))
				&& l1.getSort().getRealSort() == l2.getSort().getRealSort() ;
		for (final Entry<Term, Term> en :
				CrossProducts.binarySelectiveCrossProduct(literalTerms, false, pairSelector)) {
			nonTheoryLiteralDisequalities.add(script.term("not", script.term("=", en.getKey(), en.getValue())));
		}
		return nonTheoryLiteralDisequalities;
	}

}
