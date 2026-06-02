package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqualityRelation {

	final Map<Term, Rational> mVarToFactor;
	final Rational mResult;

	public EqualityRelation(final AffineTerm term) {
		mVarToFactor = term.getVariable2Coefficient();
		mResult = term.getConstant();
	}

	public static AffineTerm getAffineTerm(final PolynomialRelation polynomialRelation) {
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

	public Set<Term> getVars() {
		return mVarToFactor.keySet();
	}

	public List<Rational> getProtoVector(final Map<Term, Integer> varToIndex) {
		final int n = varToIndex.size() + 1;
		final List<Rational> list = new ArrayList<>(Collections.nCopies(n, Rational.ZERO));
		// TODO: list.set(0, mResult.negate());
		list.set(0, mResult);

		for (final Entry<Term, Rational> entry : mVarToFactor.entrySet()) {
			final Term variable = entry.getKey();
			final Rational factor = entry.getValue();
			final int i = varToIndex.get(variable);
			list.set(i, factor);
		}
		return list;
	}

	public MatrixQ128 getVector(final Map<Term, Integer> varToIndex) {
		final List<Rational> protoVector = getProtoVector(varToIndex);
		return CongruenceUtil.getRowVectorFromRationalList(protoVector);
	}

}
