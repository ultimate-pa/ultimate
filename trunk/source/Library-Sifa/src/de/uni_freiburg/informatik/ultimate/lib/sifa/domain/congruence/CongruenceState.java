package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceState implements IAbstractState<CongruenceState> {
	public static final CongruenceState TOP = new CongruenceState(Map.of(), ConstraintRepresentation.EMPTY);

	Map<Term, Integer> mVarToIndex;

	ConstraintRepresentation mConstraints;
	GeneratorRepresentation mGenerators;

	public CongruenceState(final Map<Term, Integer> varToIndex, final ConstraintRepresentation constraints) {
		final Map<Term, Integer> mVarToIndex = varToIndex;
		final ConstraintRepresentation mConstraints = constraints;
		final GeneratorRepresentation mGenerators = null;

		// Init, Aint it ?

	}

	public CongruenceState(final Map<Term, Integer> varToIndex, final GeneratorRepresentation generators) {
		final Map<Term, Integer> mVarToIndex = varToIndex;
		final ConstraintRepresentation mConstraints = null;
		final GeneratorRepresentation mGenerators = generators;

		// Init, Aint it ?

	}

	public ConstraintRepresentation getConstraintRepresentation() {
		if (mConstraints == null) {
			return mGenerators.computeConstraintRepresentation();
		}
		return mConstraints;
	}

	public GeneratorRepresentation getGeneratorRepresentation() {
		if (mGenerators == null) {
			return mConstraints.computeGeneratorRepresentation();
		}
		return mGenerators;
	}

	@Override
	public Term toTerm(final Script script) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CongruenceState join(final CongruenceState other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CongruenceState widen(final CongruenceState other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isBottom() {
		final ConstraintRepresentation constraints = getConstraintRepresentation();
		return constraints.isUnsat();
	}

}
