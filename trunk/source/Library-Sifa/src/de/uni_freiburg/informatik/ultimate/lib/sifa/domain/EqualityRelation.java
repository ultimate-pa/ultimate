package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqualityRelation implements ICongruenceRelation {

	final Map<Term, Rational> mVarToFactor;
	final Rational mResult;

	public EqualityRelation(final AffineTerm lhs, final Rational rhs) {
		mResult = rhs.sub(lhs.getConstant());
		final AffineTerm lhsZeroConstant = lhs.add(lhs.getConstant().negate());

		mVarToFactor = lhsZeroConstant.getVariable2Coefficient();
	}

	@Override
	public Set<Term> getVars() {
		return mVarToFactor.keySet();
	}

	@Override
	public MatrixQ128 getVector(final Map<Term, Integer> varToIndex) {
		final int n = varToIndex.size() + 1;
		final List<Rational> list = new ArrayList<>(Collections.nCopies(n, Rational.ZERO));
		list.set(0, mResult.negate());

		for (final Entry<Term, Rational> entry : mVarToFactor.entrySet()) {
			final Term variable = entry.getKey();
			final Rational factor = entry.getValue();
			final int i = varToIndex.get(variable);
			list.set(i, factor);
		}

		return CongruenceState.getRowVectorFromRationalList(list);
	}

}
