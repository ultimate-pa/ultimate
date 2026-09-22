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

	public ModuloRelation(final AffineTerm term, final BigInteger finalMod) {
		mEqualityRelation = new EqualityRelation(term);
		mMod = finalMod;
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

	private static ModuloRelation of(final Term lhs, final Term rhs, final RelationSymbol relationSymbol,
			final BigInteger modInt, final Script script) {
		final var affineTermTransformer = new AffineTermTransformer(script);
		final AffineTerm rhsAffine = (AffineTerm) affineTermTransformer.transform(rhs);
		final AffineTerm lhsAffine = (AffineTerm) affineTermTransformer.transform(lhs);
		final AffineTerm affineTerm =
				(AffineTerm) PolynomialTermOperations.sum(lhsAffine.mul(Rational.MONE), rhsAffine);

		if (affineTerm == null) {
			// We can only handle affine polynomials
			return null;
		}

		if (relationSymbol.equals(RelationSymbol.EQ)) {
			// Modulo equality
			final ModuloRelation moduloRelation = new ModuloRelation(affineTerm, modInt);
			return moduloRelation;
		}
		// Can't handle the other cases
		return null;
	}

	public static ModuloRelation of(final Term term, final Script script) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}

		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();

		final ModTerm modTermRhs = ModTerm.of(rhs);
		final ModTerm modTermLhs = ModTerm.of(lhs);

		// Checking that divisor and dividend don't contain a mod themselves
		if (modTermRhs != null) {
			if (CongruenceUtil.containsMod(modTermRhs.getDivident())) {
				return null;
			}
			if (CongruenceUtil.containsMod(modTermRhs.getDivisor())) {
				return null;
			}
		}

		if (modTermLhs != null) {
			if (CongruenceUtil.containsMod(modTermLhs.getDivident())) {
				return null;
			}
			if (CongruenceUtil.containsMod(modTermLhs.getDivisor())) {
				return null;
			}
		}

		if (modTermRhs == null && modTermLhs == null) {
			// Not a ModuloRelation
			return null;
		}
		if ((modTermRhs == null && modTermLhs != null) || (modTermRhs != null && modTermLhs == null)) {
			// We have a modulo on only one side
			// We need to have a constant on the non mod side and the modulo has to be a
			// constant
			ModTerm modSide;
			Term nonmodSide;

			if (modTermLhs != null) {
				modSide = modTermLhs;
				nonmodSide = rhs;
			} else {
				modSide = modTermRhs;
				nonmodSide = lhs;
			}

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
				// This is unsatisfiable, since modInt <= nonmodSideInt, so whatever modSide is
				// it will never match nonmodSide
				return getUnsatModuloRelation(script);
			}

			return ModuloRelation.of(finalLhs, finalRhs, relationSymbol, modInt, script);

		} else if (modTermRhs != null && modTermLhs != null) {
			// We have modulo on both sides
			// We can handle the case that the modulo on both sides is equivalent and
			// a constant

			final Term finalLhs = modTermLhs.getDivident();
			final Term finalRhs = modTermRhs.getDivident();

			final Term modLhs = modTermLhs.getDivisor();
			final Term modRhs = modTermRhs.getDivisor();

			final BigInteger modLhsInt = getConstantIntFromConstantTerm(modLhs);
			final BigInteger modRhsInt = getConstantIntFromConstantTerm(modRhs);

			if (modLhsInt == null || modRhsInt == null) {
				return null;
			}
			if (!modLhsInt.equals(modRhsInt)) {
				return null;
			}

			final BigInteger modInt = modLhsInt;

			return ModuloRelation.of(finalLhs, finalRhs, relationSymbol, modInt, script);
		}
		return null;
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
		final StringBuilder out = new StringBuilder().append(mEqualityRelation.sumString());
		out.append(" ≡").append(mMod.toString()).append(" 0");
		return out.toString();
	}

}
