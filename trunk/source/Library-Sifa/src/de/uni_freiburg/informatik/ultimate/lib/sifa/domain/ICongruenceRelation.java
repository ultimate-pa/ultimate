package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Map;
import java.util.Set;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface ICongruenceRelation {

	Set<Term> getVars();

	MatrixQ128 getVector(Map<Term, Integer> varToIndex);

}
