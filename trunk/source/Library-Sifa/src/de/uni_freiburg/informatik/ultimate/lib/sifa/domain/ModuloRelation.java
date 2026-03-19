package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ModuloRelation implements ICongruenceRelation {

	final EqualityRelation mEqualityRelation;
	final Rational mMod;

	public ModuloRelation(final AffineTerm term, final Rational mod) {
		mEqualityRelation = new EqualityRelation(term);
		mMod = mod;
	}

	@Override
	public Set<Term> getVars() {
		return mEqualityRelation.getVars();
	}

	@Override
	public MatrixQ128 getVector(final Map<Term, Integer> varToIndex) {
		List<Rational> protoVector = mEqualityRelation.getProtoVector(varToIndex);
		protoVector = protoVector.stream().map(rational -> rational.div(mMod)).collect(Collectors.toList());
		// TODO: Maybe add a modulo to everything

		return CongruenceState.getRowVectorFromRationalList(protoVector);
	}

}
