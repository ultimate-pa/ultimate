package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Map;
import java.util.Set;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ModuloRelation implements ICongruenceRelation {

	AffineTerm lhs;
	int rhs;
	int mod;

	@Override
	public Set<Term> getVars() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public MatrixQ128 getVector(final Map<Term, Integer> varToIndex) {
		// TODO Auto-generated method stub
		return null;
	}

}
