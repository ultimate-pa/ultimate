package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Map;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface ICongruenceRelation {

	MatrixQ128 getVector(Map<Term, Integer> varToIndex);
}
