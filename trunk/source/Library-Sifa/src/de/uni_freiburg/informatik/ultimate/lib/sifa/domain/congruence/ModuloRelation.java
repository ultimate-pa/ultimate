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

import java.math.BigInteger;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ModTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermOperations;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a term of the form "∑ a_i * x_i ≡b c" as the {@link EqualityRelation} for "∑ a_i * x_i = c" and the
 * constant b as a {@link BigInteger}.
 *
 * @author Max Lehr
 *
 */
public class ModuloRelation {

	private final EqualityRelation mEqualityRelation;
	private final BigInteger mMod;

	public ModuloRelation(final AffineTerm term, final BigInteger mod) {
		mEqualityRelation = new EqualityRelation(term);
		mMod = mod;
	}

	/**
	 * Returns the unsatisfiable modulo relation 1 ≡2 0.
	 */
	private static ModuloRelation getUnsatModuloRelation(final Script script) {
		final AffineTerm term = AffineTerm.constructConstant(SmtSortUtils.getIntSort(script), BigInteger.ONE);
		return new ModuloRelation(term, BigInteger.TWO);
	}

	/**
	 * Returns the constant of a constant term as a {@link BigInteger} if possible, else returns null.
	 */
	private static BigInteger getConstantIntFromConstantTerm(final Term term) {
		if (!(term instanceof ConstantTerm)) {
			return null;
		}

		final ConstantTerm constantTerm = (ConstantTerm) term;
		if (!SmtSortUtils.isIntSort(constantTerm.getSort())) {
			return null;
		}

		final Rational rational = SmtUtils.toRational(constantTerm);
		// rational will always have denuminator == 1, since we checked if its an int
		return rational.numerator();
	}

	private static ModuloRelation create(final Term lhs, final Term rhs, final BigInteger mod, final Script script) {
		final var affineTermTransformer = new AffineTermTransformer(script);
		final AffineTerm rhsAffine = (AffineTerm) affineTermTransformer.transform(rhs);
		final AffineTerm lhsAffine = (AffineTerm) affineTermTransformer.transform(lhs);
		final AffineTerm affineTerm =
				(AffineTerm) PolynomialTermOperations.sum(lhsAffine.mul(Rational.MONE), rhsAffine);

		if (affineTerm == null) {
			// We can only handle affine polynomials
			return null;
		}

		return new ModuloRelation(affineTerm, mod);
	}

	public static ModuloRelation of(final Term term, final Script script) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null || bnr.getRelationSymbol() != RelationSymbol.EQ) {
			return null;
		}

		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();

		final ModTerm modTermLhs = ModTerm.of(lhs);
		final ModTerm modTermRhs = ModTerm.of(rhs);

		if (containsNestedMod(modTermLhs) || containsNestedMod(modTermRhs)) {
			return null;
		}
		if (modTermLhs != null && modTermRhs != null) {
			return handleModuloOnBothSides(modTermLhs, modTermRhs, script);
		}
		if (modTermLhs != null) {
			return handleModuloOnSingleSide(modTermLhs, rhs, script);
		}
		if (modTermRhs != null) {
			return handleModuloOnSingleSide(modTermRhs, lhs, script);
		}
		// Not a ModuloRelation
		return null;
	}

	private static boolean containsNestedMod(final ModTerm modTerm) {
		if (modTerm == null) {
			return false;
		}
		// Checking that divisor and dividend don't contain a mod themselves
		return CongruenceUtil.containsMod(modTerm.getDivident()) || CongruenceUtil.containsMod(modTerm.getDivisor());
	}

	/**
	 * Handles the case where exactly one side of the relation is a modulo term. The other side must and the divisor
	 * must be both constants.
	 */
	private static ModuloRelation handleModuloOnSingleSide(final ModTerm modSide, final Term nonmodSide,
			final Script script) {
		final Term finalLhs = nonmodSide;
		final Term finalRhs = modSide.getDivident();
		final Term mod = modSide.getDivisor();

		final BigInteger modInt = getConstantIntFromConstantTerm(mod);
		if (modInt == null) {
			// We can only handle constant mods
			return null;
		}

		final BigInteger nonmodSideInt = getConstantIntFromConstantTerm(nonmodSide);
		if (nonmodSideInt == null) {
			// We can't handle this case
			return null;
		}

		if (modInt.compareTo(nonmodSideInt) <= 0) {
			// This is unsatisfiable, since modInt <= nonmodSideInt, so whatever modSide is it will never match
			// nonmodSide
			return getUnsatModuloRelation(script);
		}

		return create(finalLhs, finalRhs, modInt, script);
	}

	/**
	 * Handles the case where both sides are modulo terms with an equivalent, constant divisor.
	 */
	private static ModuloRelation handleModuloOnBothSides(final ModTerm modTermLhs, final ModTerm modTermRhs,
			final Script script) {
		final BigInteger modLhsInt = getConstantIntFromConstantTerm(modTermLhs.getDivisor());
		final BigInteger modRhsInt = getConstantIntFromConstantTerm(modTermRhs.getDivisor());

		if (modLhsInt == null || modRhsInt == null || !modLhsInt.equals(modRhsInt)) {
			// We can only handle the case that the modulo on both sides is equivalent and a constant
			return null;
		}

		return create(modTermLhs.getDivident(), modTermRhs.getDivident(), modLhsInt, script);
	}

	public EqualityRelation getEqualityRelation() {
		return mEqualityRelation;
	}

	public BigInteger getMod() {
		return mMod;
	}

	/**
	 * Returns the variables present in the modulo relation.
	 */
	public Set<Term> getVars() {
		return mEqualityRelation.getVars();
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder().append(mEqualityRelation.getAffineTerm());
		out.append(" ≡").append(mMod.toString()).append(" 0");
		return out.toString();
	}

}
