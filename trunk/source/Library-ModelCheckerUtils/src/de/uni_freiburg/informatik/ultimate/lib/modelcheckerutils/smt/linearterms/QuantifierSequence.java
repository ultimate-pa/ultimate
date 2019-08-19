/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Data structure that represents a quantified formula but allows one to
 * explicitly access leading quantifiers and quantified variables.
 * Two blocks with the same quantifier are merged into one block, e.g.,
 * the term ∃x.∃y x=y becomes ∃x,y. x=y
 * Furthermore we remove variables the do not occur freely in the subformula,
 * e.g., the term ∃x,y.∀x. x=y becomes ∃y.∀x. x=y
 *
 * @author Matthias Heizmann
 *
 */
public class QuantifierSequence {
	private final Script mScript;
	private final List<QuantifiedVariables> mQuantifierBlocks = new ArrayList<>();
	private Term mInnerTerm;

	public QuantifierSequence(final Script script,
			final Term input) {
		mScript = script;
		Term innerTerm = input;
		while(innerTerm instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) innerTerm;
			final Set<TermVariable> variables = SmtUtils.filterToVarsThatOccurFreelyInTerm(
					new HashSet<TermVariable>(Arrays.asList(qf.getVariables())), qf.getSubformula());
			if (!variables.isEmpty()) {
				final int quantifier = qf.getQuantifier();
				if (mQuantifierBlocks.isEmpty() || mQuantifierBlocks.get(mQuantifierBlocks.size()-1).getQuantifier() != quantifier) {
					final QuantifiedVariables qv = new QuantifiedVariables(qf.getQuantifier(), variables);
					mQuantifierBlocks.add(qv);
				} else {
					final QuantifiedVariables last = mQuantifierBlocks.remove(mQuantifierBlocks.size()-1);
					final Set<TermVariable> newQuantifiedVariables = new HashSet<>(last.getVariables());
					newQuantifiedVariables.addAll(variables);
					mQuantifierBlocks.add(new QuantifiedVariables(quantifier, newQuantifiedVariables));
				}
			}
			innerTerm = qf.getSubformula();
		}
		for (final QuantifiedVariables qb : mQuantifierBlocks) {
			if (qb.getVariables().isEmpty()) {
				throw new IllegalArgumentException("empty set not allowed");
			}
		}
		mInnerTerm = innerTerm;
	}


	/**
	 * Prepend a sequence of quantifiers to a term.
	 */
	public static Term prependQuantifierSequence(final Script script,
			final List<QuantifiedVariables> quantifierSequence, final Term term) {
		Term result = term;
		for (int i = quantifierSequence.size()-1; i>=0; i--) {
			final QuantifiedVariables quantifiedVars = quantifierSequence.get(i);
			result = script.quantifier(quantifiedVars.getQuantifier(),
					quantifiedVars.getVariables().toArray(
							new TermVariable[quantifiedVars.getVariables().size()]), result);
		}
		return result;
	}

	public Term getInnerTerm() {
		return mInnerTerm;
	}

	public Term toTerm() {
		return prependQuantifierSequence(mScript, mQuantifierBlocks, mInnerTerm);
	}

	public void replace(final Set<TermVariable> forbiddenVariables,
			final ManagedScript freshVarConstructor,
			final String replacementName) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final QuantifiedVariables qv : mQuantifierBlocks) {
			for (final TermVariable tv : forbiddenVariables) {
				if (qv.mVariables.contains(tv)) {
					final TermVariable fresh = freshVarConstructor.constructFreshTermVariable(
							replacementName, tv.getSort());
					substitutionMapping.put(tv, fresh);
					qv.mVariables.remove(tv);
					qv.mVariables.add(fresh);
				}
			}
		}
		mInnerTerm = (new Substitution(mScript, substitutionMapping)).transform(mInnerTerm);
	}

	public static Term mergeQuantifierSequences(final ManagedScript mgdScript,
			final String functionSymbolName,
			final QuantifierSequence[] quantifierSequences,
			final HashSet<TermVariable> freeVariables) {
		// sort sequences, sequence with largest number of blocks first
		Arrays.sort(quantifierSequences, Collections.reverseOrder(Comparator.comparing(
				QuantifierSequence::getNumberOfQuantifierBlocks)));

		final QuantifierSequence largestSequence = quantifierSequences[0];
		final List<QuantifiedVariables> resultQuantifierBlocks =
				new ArrayList<QuantifiedVariables>(largestSequence.getNumberOfQuantifierBlocks());
		final Term innerTerms[] = new Term[quantifierSequences.length];
		for (int i=0; i<largestSequence.getNumberOfQuantifierBlocks(); i++) {
			final int quantifierOfLargestSequence =
					largestSequence.getQuantifierBlocks().get(i).getQuantifier();
			resultQuantifierBlocks.add(new QuantifiedVariables(
					quantifierOfLargestSequence, new HashSet<>()));
		}
		assert resultQuantifierBlocks.size() == largestSequence.getNumberOfQuantifierBlocks();

		final Set<TermVariable> occurredVariables = new HashSet<>(freeVariables);
		for (int i=0; i<quantifierSequences.length; i++) {
			quantifierSequences[i].replace(occurredVariables, mgdScript, "prenex");
			// add all quantified variables to occurred Variables to avoid name clashes
			for (final QuantifiedVariables quantifiedVars : quantifierSequences[i].getQuantifierBlocks()) {
				occurredVariables.addAll(quantifiedVars.getVariables());
			}
			innerTerms[i] = quantifierSequences[i].getInnerTerm();
			if (quantifierSequences[i].getNumberOfQuantifierBlocks() > 0) {
				integrateQuantifierBlocks(resultQuantifierBlocks, quantifierSequences[i].getQuantifierBlocks());
			}
		}
		for (final QuantifiedVariables qb : resultQuantifierBlocks) {
			if (qb.getVariables().isEmpty()) {
				throw new IllegalArgumentException("empty set not allowed");
			}
		}
		final Term resultInnerTerm;
		if (functionSymbolName.equals("and")) {
			resultInnerTerm = SmtUtils.and(mgdScript.getScript(), innerTerms);
		} else if (functionSymbolName.equals("or")) {
			resultInnerTerm = SmtUtils.or(mgdScript.getScript(), innerTerms);
		} else {
			throw new IllegalArgumentException("unsupported " + functionSymbolName);
		}
		final Term result = prependQuantifierSequence(mgdScript.getScript(),
				resultQuantifierBlocks, resultInnerTerm);
		return result;
	}



	private static void integrateQuantifierBlocks(final List<QuantifiedVariables> resultQuantifierBlocks,
			final List<QuantifiedVariables> quantifierBlocks) {
		final int offset;
		{
			final int lastQuantifierResult = resultQuantifierBlocks.get(resultQuantifierBlocks.size()-1).getQuantifier();
			final int lastQuantifierCurrent = quantifierBlocks.get(quantifierBlocks.size()-1).getQuantifier();
			if (lastQuantifierResult == lastQuantifierCurrent) {
				offset = resultQuantifierBlocks.size() - quantifierBlocks.size();
			} else {
				if (resultQuantifierBlocks.size() == quantifierBlocks.size()) {
					// special case where both sequences have same size but
					// start with different quantifiers
					resultQuantifierBlocks.add(new QuantifiedVariables(lastQuantifierCurrent, new HashSet<>()));
					offset = resultQuantifierBlocks.size() - quantifierBlocks.size();
				} else {
					offset = resultQuantifierBlocks.size() - quantifierBlocks.size() - 1;
				}
			}
			assert offset >= 0;
		}
		for (int i=0; i<quantifierBlocks.size(); i++) {
			assert resultQuantifierBlocks.get(i+offset).getQuantifier() ==
					quantifierBlocks.get(i).getQuantifier() : "wrong offset";
			resultQuantifierBlocks.get(i+offset).getVariables().addAll(quantifierBlocks.get(i).getVariables());
		}
	}


	public List<QuantifiedVariables> getQuantifierBlocks() {
		return mQuantifierBlocks;
	}

	public int getNumberOfQuantifierBlocks() {
		return mQuantifierBlocks.size();
	}

	@Override
	public String toString() {
		return mQuantifierBlocks + " " + mInnerTerm;
	}

	public String buildQuantifierSequenceStringRepresentation() {
		final StringBuilder sb = new StringBuilder();
		for (final QuantifiedVariables qb : mQuantifierBlocks) {
			sb.append(QuantifierUtils.getAsciiAbbreviation(qb.getQuantifier()));
		}
		return sb.toString();
	}


	public static class QuantifiedVariables {
		private final int mQuantifier;
		private final Set<TermVariable> mVariables;
		public QuantifiedVariables(final int quantifier, final Set<TermVariable> variables) {
			super();
			mQuantifier = quantifier;
			mVariables = variables;
		}
		public int getQuantifier() {
			return mQuantifier;
		}
		public Set<TermVariable> getVariables() {
			return mVariables;
		}
		@Override
		public String toString() {
			return ((mQuantifier == 0) ? "exists" : "forall") + mVariables + ". ";
		}


	}

}
