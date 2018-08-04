/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/*
 * TODO: Comment.
 */
public class MoNatDiffUtils {

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntSort(Sort sort) {
		return sort.getName().equals("SetOfInt");
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntConstant(Term term) {
		return term instanceof ConstantTerm && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeIntVariable(Term term) {
		return SmtUtils.isConstant(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeSetOfIntVariable(Term term) {
		return SmtUtils.isConstant(term) && isSetOfIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedIntVariable(Term term) {
		return term instanceof TermVariable && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedSetOfIntVariable(Term term) {
		return term instanceof TermVariable && isSetOfIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeVariable(Term term) {
		return isFreeIntVariable(term) || isFreeSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedVariable(Term term) {
		return isQuantifiedIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isVariable(Term term) {
		return isFreeVariable(term) || isQuantifiedVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntVariable(Term term) {
		return isFreeIntVariable(term) || isQuantifiedIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntVariable(Term term) {
		return isFreeSetOfIntVariable(term) || isQuantifiedSetOfIntVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<MoNatDiffAlphabetSymbol> allMatchesAlphabet(Set<MoNatDiffAlphabetSymbol> alphabet, Boolean value,
			Term... excludedTerms) {

		Set<MoNatDiffAlphabetSymbol> result = new HashSet<MoNatDiffAlphabetSymbol>();
		Iterator<MoNatDiffAlphabetSymbol> it = alphabet.iterator();

		while (it.hasNext()) {
			MoNatDiffAlphabetSymbol symbol = it.next();
			if (symbol.allMatches(value, excludedTerms))
				result.add(symbol);
		}

		return result;
	}

	/*
	 * TODO: Comment.
	 */
	public static Set<String> hierarchicalSuccessorsOutgoing(
			INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, String state,
			MoNatDiffAlphabetSymbol... symbols) {

		Set<String> result = new HashSet<String>();

		for (MoNatDiffAlphabetSymbol symbol : symbols) {
			Iterator<OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String>> it = automaton
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
			INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, String state,
			MoNatDiffAlphabetSymbol... symbols) {

		Set<String> result = new HashSet<String>();

		for (MoNatDiffAlphabetSymbol symbol : symbols) {
			Iterator<IncomingInternalTransition<MoNatDiffAlphabetSymbol, String>> it = automaton
					.internalPredecessors(state, symbol).iterator();

			while (it.hasNext())
				result.add(it.next().getPred());
		}

		return result;
	}
}