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

	private final Map<Term, Rational> mVarToFactor;
	private final Rational mResult;

	public EqualityRelation(final AffineTerm term) {
		mVarToFactor = term.getVariable2Coefficient();
		mResult = term.getConstant();
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
		return mVarToFactor;
	}

	public Rational getResult() {
		return mResult;
	}

	/**
	 * Returns the variables present in the equality relation.
	 */
	public Set<Term> getVars() {
		return mVarToFactor.keySet();
	}

	public String sumString() {
		final StringBuilder out = new StringBuilder();

		for (final Term var : mVarToFactor.keySet()) {
			final Rational factor = mVarToFactor.get(var);

			if (factor.equals(Rational.MONE)) {
				out.append("-");
			} else if (!factor.equals(Rational.ONE)) {
				out.append(factor.toString()).append("*");
			}
			out.append(var.toString()).append(" + ");
		}
		out.append(mResult.toString());

		return out.toString();
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder().append(sumString());
		out.append(" = 0");
		return out.toString();
	}

}
