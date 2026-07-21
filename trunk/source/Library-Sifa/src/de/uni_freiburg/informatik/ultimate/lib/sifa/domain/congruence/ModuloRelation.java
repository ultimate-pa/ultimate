package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ModTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermOperations;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ModuloRelation {
	public static BigInteger MAX_NEG_MOD_COUNT = BigInteger.valueOf(5);

	final EqualityRelation mEqualityRelation;
	final BigInteger mMod;

	public ModuloRelation(final AffineTerm term, final BigInteger finalMod) {
		mEqualityRelation = new EqualityRelation(term);
		mMod = finalMod;
	}

	private static ModuloRelation getUnsatModuloRelation(final Script script) {
		final AffineTerm term = AffineTerm.constructConstant(SmtSortUtils.getIntSort(script), BigInteger.ONE);
		return new ModuloRelation(term, BigInteger.TWO);
	}

	public static BigInteger getConstantIntFromConstantTerm(final Term term) {
		if (!(term instanceof ConstantTerm)) {
			return null;
		}

		final ConstantTerm constantTerm = (ConstantTerm) term;
		if (!SmtSortUtils.isIntSort(constantTerm.getSort())) {
			return null;
		}

		final Rational rational = SmtUtils.toRational(constantTerm);
		// rationalMod will always have denuminator == 1, since we checked if its an int
		return rational.numerator();
	}

	public static List<ModuloRelation> of(final Term lhs, final Term rhs, final RelationSymbol relationSymbol,
			final BigInteger modInt, final Script script) {
		final var affineTermTransformer = new AffineTermTransformer(script);
		final AffineTerm rhsAffine = (AffineTerm) affineTermTransformer.transform(rhs);
		final AffineTerm lhsAffine = (AffineTerm) affineTermTransformer.transform(lhs);
		final AffineTerm affineTerm = (AffineTerm) PolynomialTermOperations.sum(lhsAffine.mul(Rational.MONE),
				rhsAffine);

		if (affineTerm == null) {
			// We can only handle affine polynomials
			return List.of();
		}

		if (relationSymbol.equals(RelationSymbol.EQ)) {
			// Modulo equality
			final ModuloRelation moduloRelation = new ModuloRelation(affineTerm, modInt);
			return List.of(moduloRelation);
			// TODO: Remove the other cases
		} else if (relationSymbol.equals(RelationSymbol.DISTINCT) && modInt.compareTo(MAX_NEG_MOD_COUNT) <= 0) {
			// Have an inequality with a mod value that's small enough
			final List<ModuloRelation> list = new ArrayList<>();

			for (BigInteger i = BigInteger.ONE; i.compareTo(modInt) < 0; i = i.add(BigInteger.ONE)) {
				final AffineTerm offsetAffineTerm = affineTerm.add(Rational.valueOf(i, BigInteger.ONE));
				final ModuloRelation moduloRelation = new ModuloRelation(offsetAffineTerm, modInt);
				list.add(moduloRelation);
			}
			return list;
		} else {
			// Can't handle the other cases
			// TODO: Overthink these cases again
			return List.of();
		}
	}

	public static List<ModuloRelation> of(final Term term, final Script script) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return List.of();
		}

		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();

		final ModTerm modTermRhs = ModTerm.of(rhs);
		final ModTerm modTermLhs = ModTerm.of(lhs);

		// Checking that divisor and dividend don't contain a mod themselves
		final var checker = new SubtermPropertyChecker(x -> SmtUtils.isFunctionApplication(x, "mod"));
		if (modTermRhs != null) {
			if (checker.isSatisfiedBySomeSubterm(modTermRhs.getDivident())) {
				return List.of();
			}
			if (checker.isSatisfiedBySomeSubterm(modTermRhs.getDivisor())) {
				return List.of();
			}
		}

		if (modTermLhs != null) {
			if (checker.isSatisfiedBySomeSubterm(modTermLhs.getDivident())) {
				return List.of();
			}
			if (checker.isSatisfiedBySomeSubterm(modTermLhs.getDivisor())) {
				return List.of();
			}
		}

		if (modTermRhs == null && modTermLhs == null) {
			// Not a ModuloRelation
			return null;
		}
		if ((modTermRhs == null && modTermLhs != null) || (modTermRhs != null && modTermLhs == null)) {
			// We have a modulo on only one side
			// We need to have constant on the non mod side
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
				return List.of();
			}

			final BigInteger nonmodSideInt = getConstantIntFromConstantTerm(nonmodSide);
			if (nonmodSideInt == null) {
				// We can't handle this case
				return List.of();
			}

			if (modInt.compareTo(nonmodSideInt) <= 0) {
				// This is unsatisfiable, since modInt <= nonmodSideInt, so whatever modSide is
				// it will never match nonmodSide
				return List.of(getUnsatModuloRelation(script));
			}

			return ModuloRelation.of(finalLhs, finalRhs, relationSymbol, modInt, script);

		} else if (modTermRhs != null && modTermLhs != null) {
			// We have modulo on both sides
			// We can handle the case that the modulo on both sides is equivalent and
			// constant

			final Term finalLhs = modTermLhs.getDivident();
			final Term finalRhs = modTermRhs.getDivident();

			final Term modLhs = modTermLhs.getDivisor();
			final Term modRhs = modTermRhs.getDivisor();

			final BigInteger modLhsInt = getConstantIntFromConstantTerm(modLhs);
			final BigInteger modRhsInt = getConstantIntFromConstantTerm(modRhs);

			if (modLhsInt == null || modRhsInt == null) {
				return List.of();
			}
			if (!modLhsInt.equals(modRhsInt)) {
				return List.of();
			}

			final BigInteger modInt = modLhsInt;

			return ModuloRelation.of(finalLhs, finalRhs, relationSymbol, modInt, script);
		}
		return null;
	}

	public Set<Term> getVars() {
		return mEqualityRelation.getVars();
	}

	private static Rational modRational(final Rational rational, final BigInteger mod) {
		if (rational.denominator().equals(BigInteger.ONE)) {
			final BigInteger newNumerator = rational.numerator().mod(mod);
			return Rational.valueOf(newNumerator, BigInteger.ONE);
		}
		return rational;
	}

	public RationalVector getVector(final Map<Term, Integer> varToIndex) {
		final List<Rational> protoVector = mEqualityRelation.getProtoVector(varToIndex);
		// TODO: What does following line do when modInt is 2^32 ?
		final List<Rational> modProtoVector = protoVector.stream().map(rational -> modRational(rational, mMod))
				.collect(Collectors.toList());
		final Rational rationalMod = Rational.valueOf(mMod, BigInteger.ONE);
		final List<Rational> divProtoVector = modProtoVector.stream().map(rational -> rational.div(rationalMod))
				.collect(Collectors.toList());

		return new RationalVector(divProtoVector);
	}

}
