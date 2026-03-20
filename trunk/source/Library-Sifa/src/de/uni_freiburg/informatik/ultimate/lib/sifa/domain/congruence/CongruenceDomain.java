package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StateBasedDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ModTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceDomain extends StateBasedDomain<CongruenceState> {

	public CongruenceDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new CongruenceStateProvider(tools.getScript()));
		// TODO Auto-generated constructor stub
	}

	private static class CongruenceStateProvider implements IStateProvider<CongruenceState> {

		private final Script mScript;
		public BigInteger MAX_NEG_MOD_COUNT = BigInteger.valueOf(5);

		public CongruenceStateProvider(final Script script) {
			mScript = script;
		}

		public static AffineTerm toAffineTerm(final PolynomialRelation polynomialRelation) {
			final AbstractGeneralizedAffineTerm<?> polynomialTerm = polynomialRelation.getPolynomialTerm();
			if (!polynomialTerm.isAffine()) {
				return null;
			}

			return (AffineTerm) polynomialTerm;
		}

		public List<ICongruenceRelation> toCongruenceRelation(final Term term) {
			// TODO: Change into two things: One for equalities, one for congruences
			final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
			if (bnr == null) {
				return List.of();
			}

			final Term lhs = bnr.getLhs();
			final Term rhs = bnr.getRhs();
			final RelationSymbol relationSymbol = bnr.getRelationSymbol();

			final ModTerm modRhs = ModTerm.of(rhs);
			final ModTerm modLhs = ModTerm.of(lhs);

			// TODO: VERY IMPORTANT: We can only handle other stuff see notes

			if (modRhs == null && modLhs == null) {
				if (!relationSymbol.equals(RelationSymbol.EQ)) {
					return List.of();
				}
				// We have a normal equality

				final PolynomialRelation polynomialRelation = PolynomialRelation.of(mScript, relationSymbol, lhs, rhs);
				final AffineTerm affineTerm = toAffineTerm(polynomialRelation);
				// TODO: Handle affineTerm == null
				final EqualityRelation equalityRelation = new EqualityRelation(affineTerm);
				return List.of(equalityRelation);
			}
			if ((modRhs == null && modLhs != null) || (modRhs != null && modLhs == null)) {
				// We have a modulo on only one side
				ModTerm modSide;
				Term nonmodSide;

				if (modLhs != null) {
					modSide = modLhs;
					nonmodSide = rhs;
				} else {
					modSide = modRhs;
					nonmodSide = lhs;
				}

				final Term finalLhs = nonmodSide;
				final Term finalRhs = modSide.getDivident();
				final Term mod = modSide.getDivisor();

				if (!(mod instanceof ConstantTerm)) {
					return List.of();
				}

				final ConstantTerm constantMod = (ConstantTerm) mod;
				if (!SmtSortUtils.isIntSort(constantMod.getSort())) {
					return List.of();
				}

				// TODO: Make sure that this does not crash
				final Rational rationalMod = SmtUtils.toRational(constantMod);
				// TODO: rationalMod will always have denuminator == 1, since we checked if its
				// an int, this simplifies a bunch of stuff

				final BigInteger finalMod = rationalMod.numerator();
				final Rational multiplier = Rational.valueOf(rationalMod.denominator(), BigInteger.ONE);

				PolynomialRelation polynomialRelation = PolynomialRelation.of(mScript, relationSymbol, finalLhs,
						finalRhs);
				polynomialRelation = polynomialRelation.mul(mScript, multiplier);
				final AffineTerm affineTerm = toAffineTerm(polynomialRelation);

				// TODO: Check if affineTerm == null

				if (relationSymbol.equals(RelationSymbol.EQ)) {
					// Modulo equality
					final ModuloRelation moduloRelation = new ModuloRelation(affineTerm, finalMod);
					return List.of(moduloRelation);
				} else if (relationSymbol.equals(RelationSymbol.DISTINCT)
						&& finalMod.compareTo(MAX_NEG_MOD_COUNT) <= 0) {
					// Have an inequality with a mod value that's small enough
					final List<ICongruenceRelation> list = new ArrayList<>();

					for (int i = 1; i < finalMod.intValue(); i++) {
						final AffineTerm offsetAffineTerm = affineTerm
								.add(Rational.valueOf(BigInteger.valueOf(i), BigInteger.ONE));
						final ModuloRelation moduloRelation = new ModuloRelation(offsetAffineTerm, finalMod);
						list.add(moduloRelation);
					}
					return list;
				} else {
					// Can't handle the other cases
					// TODO: Overthink these cases again
					return List.of();
				}

			} else if (modRhs != null && modLhs != null) {
				// We have modulo on both sides
				// TODO Figure out if this can be handled
				// Maybe with limit to same mod on each side
				return List.of();
			}

			// This should not be able to get reached
			return null;
		}

		@Override
		public CongruenceState toState(final Term[] conjuncts) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CongruenceState getTopState() {
			return CongruenceState.TOP;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			// TODO Auto-generated method stub
			return term;
		}

	}

}