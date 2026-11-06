/*
 * Copyright (C) 2026 Max Lehr
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a term of the form "∑ a_i * x_i = c" as a mapping from variables x_i to their respective factors a_i and
 * the constant c as a {@link Rational}.
 *
 * @author Max Lehr
 *
 */
public class EqualityRelation {
	private final AffineTerm mAffineTerm;

	public EqualityRelation(final AffineTerm term) {
		mAffineTerm = term;
	}

	/**
	 * Extracts the affine term out of the polynomialRelation if possible, else returns null.
	 */
	private static AffineTerm getAffineTerm(final PolynomialRelation polynomialRelation) {
		final AbstractGeneralizedAffineTerm<?> polynomialTerm = polynomialRelation.getPolynomialTerm();
		if (!polynomialTerm.isAffine()) {
			return null;
		}
		return (AffineTerm) polynomialTerm;
	}

	public static EqualityRelation of(final Term term, final Script script) {
		final PolynomialRelation polynomialRelation = PolynomialRelation.of(script, term);
		if (polynomialRelation == null) {
			return null;
		}
		if (!polynomialRelation.getRelationSymbol().equals(RelationSymbol.EQ)) {
			return null;
		}
		final AffineTerm affineTerm = getAffineTerm(polynomialRelation);
		if (affineTerm == null) {
			return null;
		}
		return new EqualityRelation(affineTerm);
	}

	public Map<Term, Rational> getVarToFactor() {
		return mAffineTerm.getVariable2Coefficient();
	}

	public Rational getConstant() {
		return mAffineTerm.getConstant();
	}

	/**
	 * Returns the variables present in the equality relation.
	 */
	public Set<Term> getVars() {
		return getVarToFactor().keySet();
	}

	public AffineTerm getAffineTerm() {
		return mAffineTerm;
	}

	@Override
	public String toString() {
		return mAffineTerm + " = 0";
	}

}
