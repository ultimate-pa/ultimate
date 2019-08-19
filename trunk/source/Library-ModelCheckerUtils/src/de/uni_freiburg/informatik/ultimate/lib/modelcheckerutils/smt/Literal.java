/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a boolean term where we explicitly store if the term is negated or not.
 * {@link http://en.wikipedia.org/wiki/Literal_%28mathematical_logic%29} This data structure representa a term φ as a
 * pair (φ_atom, plrty) where atom is a Boolean term and plrty has either the value POSITIVE or NEGATIVE. The pair
 * (φ_atom, POSITIVE) represents the term φ_atom. the pair (φ_atom, NEGATIVE) represents the term (not φ_atom). We call
 * φ_atom the atom of this literal. We call plrty the polarity of this literal.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Literal {

	public enum Polarity {
		POSITIVE, NEGATIVE
	}

	private final Term mAtom;
	private final Polarity mPolarity;

	/**
	 * Convert a Boolean term into this representation. If the input Term is negated several times, we strip all
	 * negation symbols.
	 */
	public Literal(Term input) {
		super();
		if (!SmtSortUtils.isBoolSort(input.getSort())) {
			throw new IllegalArgumentException("only applicable to sort Bool");
		}
		Term withoutNegation = null;
		int removedNegationSymbols = 0;
		do {
			withoutNegation = getParameterOfNotTerm(input);
			if (withoutNegation != null) {
				input = withoutNegation;
				removedNegationSymbols++;
			}

		} while (withoutNegation != null);
		if (removedNegationSymbols % 2 == 0) {
			mPolarity = Polarity.POSITIVE;
		} else {
			mPolarity = Polarity.NEGATIVE;
		}
		mAtom = input;
	}

	public Term getAtom() {
		return mAtom;
	}

	public Polarity getPolarity() {
		return mPolarity;
	}

	public Term toTerm(final Script script) {
		if (mPolarity == Polarity.POSITIVE) {
			return mAtom;
		}
		return script.term("not", mAtom);
	}

	/**
	 * If term is a negation, i.e. of the form "(not φ)" return the argument of the negation φ, otherwise return null.
	 */
	public static Term getParameterOfNotTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("not")) {
				assert appTerm.getParameters().length == 1;
				return appTerm.getParameters()[0];
			}
		}
		return null;
	}

}
