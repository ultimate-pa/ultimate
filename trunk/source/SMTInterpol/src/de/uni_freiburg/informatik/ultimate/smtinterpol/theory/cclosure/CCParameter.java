/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * A value of the form {@code getCCTerm() + getOffset()}: a CCTerm together with a constant offset. This is what every
 * consumer of a function application argument actually deals with once offset equalities exist (the argument of
 * {@code f(x+5)} is the CCTerm {@code x} plus the offset {@code 5}), as well as array indices, congruence arguments and
 * shared-term comparisons.
 *
 * <p>A bare {@link CCTerm} <em>is</em> a {@code CCParameter} with offset {@link Rational#ZERO}, so the common offset-free
 * case needs no wrapper object; only non-zero offsets allocate an {@link OffsettedCCTerm}. Use {@link #of} to build one
 * with this canonicalization.
 *
 * <p>The <em>value identity</em> of a parameter is the pair {@code (getRepresentative(), getOffsetToRep())}: two
 * parameters denote the same value iff they agree on both. Note this identity changes when the underlying class is
 * merged (the representative and its offset shift), so it must not be used as a key in a map that persists across
 * merges; see {@link #sameValueAs}.
 *
 * @author Jochen Hoenicke
 */
public interface CCParameter {

	/** The underlying CCTerm. */
	CCTerm getCCTerm();

	/** The constant offset added to the CCTerm; {@link Rational#ZERO} for a bare {@link CCTerm}. */
	Rational getOffset();

	/**
	 * The SMT-LIB term denoting this value: the underlying term when the offset is zero, otherwise {@code (+ term
	 * offset)} (or a plain constant when the underlying term is the constant {@code 0}). A bare {@link CCTerm} returns
	 * its own flat term unchanged, so offset-free uses are byte-identical; only a non-zero (necessarily numeric) offset
	 * builds the sum.
	 */
	Term getFlatTerm();

	/** The representative of the underlying CCTerm's congruence class. */
	default CCTerm getRepresentative() {
		return getCCTerm().getRepresentative();
	}

	/** The offset of this value relative to the representative: {@code value == value(representative) + this}. */
	default Rational getOffsetToRep() {
		return getCCTerm().getOffsetToRep().add(getOffset());
	}

	/** Whether this and the other parameter currently denote the same value (same representative and offset). */
	default boolean sameValueAs(final CCParameter other) {
		return getRepresentative() == other.getRepresentative() && getOffsetToRep().equals(other.getOffsetToRep());
	}

	/**
	 * A canonical key for this value, suitable as a map key within a single snapshot (e.g. while the array theory
	 * rebuilds its structures). It is built from the representative, so its {@code equals}/{@code hashCode} (the bare
	 * representative for offset zero, an {@link OffsettedCCTerm} over {@code (representative, offsetToRep)} otherwise)
	 * coincide with value identity. The key changes when the class is merged, so it must be rebuilt after merges, not
	 * stored across them.
	 */
	default CCParameter getValueKey() {
		return CCParameter.of(getRepresentative(), getOffsetToRep());
	}

	/**
	 * Build a parameter for {@code term + offset}, returning the bare term when the offset is zero so that the common
	 * case allocates nothing.
	 */
	static CCParameter of(final CCTerm term, final Rational offset) {
		return offset.equals(Rational.ZERO) ? term : new OffsettedCCTerm(term, offset);
	}

	/**
	 * Build the SMT term {@code term + offset} as a <em>flattened</em> sum: when {@code term} is itself a {@code +}
	 * application, its summands are spliced in rather than nested, so the result is {@code (+ z w offset)} rather than
	 * {@code (+ (+ z w) offset)}. This matters because the proof checker parses a {@code +} term with the non-recursive
	 * {@link de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial} (only the top level is flattened); a nested
	 * sum would be treated as an opaque monomial and could not be related arithmetically to the original flat parameter
	 * term that the {@link de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermBuilder} split into this
	 * {@code (base, offset)} pair. Flattening reconstructs that original parameter term.
	 *
	 * <p>A constant {@code term} (the base {@code 0} of a plain-numeral parameter) folds into a plain constant, e.g.
	 * {@code 5} rather than {@code (+ 0 5)}, matching the canonic term of that value. A zero offset returns
	 * {@code term} unchanged.
	 */
	static Term addConstant(final Term term, final Rational offset) {
		if (offset.equals(Rational.ZERO)) {
			return term;
		}
		final Rational termValue = Polynomial.parseConstant(term);
		if (termValue != null) {
			return termValue.add(offset).toTerm(term.getSort());
		}
		final Term offsetTerm = offset.toTerm(term.getSort());
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("+")) {
			final Term[] inner = ((ApplicationTerm) term).getParameters();
			final Term[] args = new Term[inner.length + 1];
			System.arraycopy(inner, 0, args, 0, inner.length);
			args[inner.length] = offsetTerm;
			return term.getTheory().term("+", args);
		}
		return term.getTheory().term("+", term, offsetTerm);
	}
}
