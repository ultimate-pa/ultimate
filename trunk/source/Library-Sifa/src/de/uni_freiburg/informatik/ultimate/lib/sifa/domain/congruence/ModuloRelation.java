package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ModTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ModuloRelation implements ICongruenceRelation {
	public static BigInteger MAX_NEG_MOD_COUNT = BigInteger.valueOf(5);

	final EqualityRelation mEqualityRelation;
	final Rational mMod;

	public ModuloRelation(final AffineTerm term, final BigInteger finalMod) {
		mEqualityRelation = new EqualityRelation(term);
		mMod = Rational.valueOf(finalMod, BigInteger.ONE);
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
		final PolynomialRelation polynomialRelation = PolynomialRelation.of(script, relationSymbol, lhs, rhs);
		final AffineTerm affineTerm = EqualityRelation.getAffineTerm(polynomialRelation);

		if (affineTerm == null) {
			// We can only handle affine polynomials
			return List.of();
		}

		if (relationSymbol.equals(RelationSymbol.EQ)) {
			// Modulo equality
			final ModuloRelation moduloRelation = new ModuloRelation(affineTerm, modInt);
			return List.of(moduloRelation);
		} else if (relationSymbol.equals(RelationSymbol.DISTINCT) && modInt.compareTo(MAX_NEG_MOD_COUNT) <= 0) {
			// Have an inequality with a mod value that's small enough
			final List<ModuloRelation> list = new ArrayList<>();

			for (final BigInteger i = BigInteger.ONE; i.compareTo(modInt) < 0; i.add(BigInteger.ONE)) {
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
			if (!modLhsInt.equals(modTermRhs)) {
				return List.of();
			}

			final BigInteger modInt = modLhsInt;

			return ModuloRelation.of(finalLhs, finalRhs, relationSymbol, modInt, script);
		}
		return null;
	}

	@Override
	public Set<Term> getVars() {
		return mEqualityRelation.getVars();
	}

	@Override
	public MatrixQ128 getVector(final Map<Term, Integer> varToIndex) {
		final List<Rational> protoVector = mEqualityRelation.getProtoVector(varToIndex);
		// TODO: Maybe add a modulo to everything before dividing
		final List<Rational> divProtoVector = protoVector.stream().map(rational -> rational.div(mMod))
				.collect(Collectors.toList());

		return CongruenceUtil.getRowVectorFromRationalList(divProtoVector);
	}

}
