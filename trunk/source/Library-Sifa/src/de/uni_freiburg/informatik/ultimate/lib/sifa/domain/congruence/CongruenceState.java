package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.List;
import java.util.Map;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceState implements IAbstractState<CongruenceState> {
	public static final CongruenceState TOP = new CongruenceState(Map.of(), ConstraintRepresentation.getEmpty(0));

	private Map<Term, Integer> mVarToIndex;

	private ConstraintRepresentation mConstraints;
	private GeneratorRepresentation mGenerators;

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

	public Map<Term, Integer> getVarToIndex() {
		return mVarToIndex;
	}

	@Override
	public Term toTerm(final Script script) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CongruenceState join(final CongruenceState other) {
		// Compute the new VarToIndex
		final Map<Term, Integer> selfVarToIndex = getVarToIndex();
		final Map<Term, Integer> otherVarToIndex = other.getVarToIndex();
		final Map<Term, Integer> newVarToIndex = CongruenceUtil.mergeMaps(selfVarToIndex, otherVarToIndex);

		// Compute the required lengths for the vectors.
		// +1 for the constant in the first place
		final int newColumnCount = newVarToIndex.size() + 1;

		// Compute the reordered forms of the generators
		final Map<Integer, Integer> selfReorderMap = CongruenceUtil.getReorderForMaps(selfVarToIndex, newVarToIndex);
		selfReorderMap.put(0, 0);
		final GeneratorRepresentation selfGenerators = getGeneratorRepresentation();
		final GeneratorRepresentation selfReorderedGenerators = selfGenerators.getReorderedForm(selfReorderMap,
				newColumnCount);

		final Map<Integer, Integer> otherReorderMap = CongruenceUtil.getReorderForMaps(otherVarToIndex, newVarToIndex);
		otherReorderMap.put(0, 0);
		final GeneratorRepresentation otherGenerators = other.getGeneratorRepresentation();
		final GeneratorRepresentation otherReorderedGenerators = otherGenerators.getReorderedForm(otherReorderMap,
				newColumnCount);

		// Combine the generators
		final List<MatrixQ128> newLines = selfReorderedGenerators.getLines();
		newLines.addAll(otherReorderedGenerators.getLines());

		final List<MatrixQ128> newParameters = selfReorderedGenerators.getParameters();
		newParameters.addAll(otherReorderedGenerators.getParameters());

		final GeneratorRepresentation newGenerators = new GeneratorRepresentation(newLines, newParameters, newColumnCount);

		return new CongruenceState(newVarToIndex, newGenerators);
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
