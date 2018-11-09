/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;

/*
 * TODO: Comment.
 */
public final class MoNatDiffUtils {

	private MoNatDiffUtils() {

	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntSort(final Sort sort) {
		return sort.getName().equals("SetOfInt");
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntConstant(final Term term) {
		return term instanceof ConstantTerm && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeIntVariable(final Term term) {
		return SmtUtils.isConstant(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeSetOfIntVariable(final Term term) {
		return SmtUtils.isConstant(term) && isSetOfIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedIntVariable(final Term term) {
		return term instanceof TermVariable && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedSetOfIntVariable(final Term term) {
		return term instanceof TermVariable && isSetOfIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeVariable(final Term term) {
		return isFreeIntVariable(term) || isFreeSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedVariable(final Term term) {
		return isQuantifiedIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isVariable(final Term term) {
		return isFreeVariable(term) || isQuantifiedVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntVariable(final Term term) {
		return isFreeIntVariable(term) || isQuantifiedIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntVariable(final Term term) {
		return isFreeSetOfIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static AffineTerm makeAffineTerm(final Script script, final Term term, final ILogger logger) {
		final AffineTerm affineTerm = (AffineTerm)new AffineTermTransformer(script).transform(term);

		if (affineTerm.isErrorTerm())
			throw new IllegalArgumentException("Could not transform input to AffineTerm.");

		// return (AffineTerm) affineTerm.toTerm(script);
		
		return affineTerm;
	}

	/*
	 * TODO: Comment.
	 */
	public static AffineRelation makeAffineRelation(final Script script, final Term term,
			final TransformInequality transformInequality) {

		AffineRelation affineRelation = null;

		try {
			affineRelation = new AffineRelation(script, term, transformInequality);
		} catch (final NotAffineException e) {
			throw new IllegalArgumentException("Could not transform input to AffineRelation.");
		}

		return affineRelation;
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<MoNatDiffAlphabetSymbol> createAlphabet(final Term[] terms) {
		final Set<MoNatDiffAlphabetSymbol> result = new HashSet<MoNatDiffAlphabetSymbol>();

		if (terms.length == 0) {
			result.add(new MoNatDiffAlphabetSymbol());
			return result;
		}

		for (int i = 0; i < Math.pow(2, terms.length); i++) {
			final MoNatDiffAlphabetSymbol symbol = new MoNatDiffAlphabetSymbol();

			for (int j = 0; j < terms.length; j++) {
				final int value = (i / (int) Math.pow(2, j)) % 2;
				symbol.add(terms[j], value);
			}
			result.add(symbol);
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<MoNatDiffAlphabetSymbol> mergeAlphabets(final Set<MoNatDiffAlphabetSymbol> alphabet1,
			final Set<MoNatDiffAlphabetSymbol> alphabet2) {

		final Set<Term> terms = new HashSet<Term>();
		terms.addAll(alphabet1.iterator().next().getMap().keySet());
		terms.addAll(alphabet2.iterator().next().getMap().keySet());

		return createAlphabet(terms.toArray(new Term[terms.size()]));
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<MoNatDiffAlphabetSymbol> allMatchesAlphabet(final Set<MoNatDiffAlphabetSymbol> alphabet,
			final Boolean value, final Term... excludedTerms) {

		final Set<MoNatDiffAlphabetSymbol> result = new HashSet<MoNatDiffAlphabetSymbol>();
		final Iterator<MoNatDiffAlphabetSymbol> it = alphabet.iterator();

		while (it.hasNext()) {
			final MoNatDiffAlphabetSymbol symbol = it.next();
			if (symbol.allMatches(value, excludedTerms))
				result.add(symbol);
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<String> hierarchicalSuccessorsOutgoing(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final String state,
			final MoNatDiffAlphabetSymbol... symbols) {

		final Set<String> result = new HashSet<String>();

		for (final MoNatDiffAlphabetSymbol symbol : symbols) {
			final Iterator<OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String>> it = automaton
					.internalSuccessors(state, symbol).iterator();

			while (it.hasNext())
				result.add(it.next().getSucc());
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<String> hierarchicalPredecessorsIncoming(
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final String state,
			final MoNatDiffAlphabetSymbol... symbols) {

		final Set<String> result = new HashSet<String>();

		for (final MoNatDiffAlphabetSymbol symbol : symbols) {
			final Iterator<IncomingInternalTransition<MoNatDiffAlphabetSymbol, String>> it = automaton
					.internalPredecessors(state, symbol).iterator();

			while (it.hasNext())
				result.add(it.next().getPred());
		}

		return result;
	}
}