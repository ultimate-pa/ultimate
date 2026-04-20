package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceState implements IAbstractState<CongruenceState> {
	public static final CongruenceState TOP = new CongruenceState(Map.of(), ConstraintRepresentation.getEmpty(0));

	private final Map<Term, Integer> mVarToIndex;

	private final ConstraintRepresentation mConstraints;
	private final GeneratorRepresentation mGenerators;

	public CongruenceState(final Map<Term, Integer> varToIndex, final ConstraintRepresentation constraints) {
		mVarToIndex = varToIndex;
		mConstraints = constraints;
		mGenerators = null;

		// Init, Aint it ?

	}

	public CongruenceState(final Map<Term, Integer> varToIndex, final GeneratorRepresentation generators) {
		mVarToIndex = varToIndex;
		mConstraints = null;
		mGenerators = generators;

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

	private Map<Integer, Term> getIndexToVar() {
		final Map<Integer, Term> indexToVar = new HashMap<>();
		final Map<Term, Integer> varToIndex = getVarToIndex();

		for (final Term term : varToIndex.keySet()) {
			final Integer index = varToIndex.get(term);
			indexToVar.put(index, term);
		}
		return indexToVar;
	}

	@Override
	public Term toTerm(final Script script) {
		final ConstraintRepresentation constraints = getConstraintRepresentation();
		final List<MatrixQ128> equalities = constraints.getEqualities();
		final List<MatrixQ128> congruences = constraints.getCongruences();

		final Map<Integer, Term> indexToVar = getIndexToVar();

		final Set<Term> terms = new HashSet<>();

		for (final MatrixQ128 equality : equalities) {
			final long commonDenominator = CongruenceUtil.getCommonDenominator(equality);
			final MatrixQ128 wholeEquality = equality.multiply(commonDenominator);
			final Term sum = CongruenceUtil.getSumTerm(wholeEquality, indexToVar, script);
			final Term equalityTerm = SmtUtils.binaryEquality(script, sum,
					SmtUtils.constructIntValue(script, BigInteger.ZERO));
			terms.add(equalityTerm);
		}

		for (final MatrixQ128 congruence : congruences) {
			final long commonDenominator = CongruenceUtil.getCommonDenominator(congruence);
			final MatrixQ128 wholeCongruence = congruence.multiply(commonDenominator);
			final Term sum = CongruenceUtil.getSumTerm(wholeCongruence, indexToVar, script);
			final Term modTerm = SmtUtils.constructIntValue(script, BigInteger.valueOf(commonDenominator));
			final Term modSum = SmtUtils.mod(script, sum, modTerm);
			final Term congruenceTerm = SmtUtils.binaryEquality(script, modSum,
					SmtUtils.constructIntValue(script, BigInteger.ZERO));
			terms.add(congruenceTerm);
		}

		return SmtUtils.and(script, terms);
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

		final GeneratorRepresentation newGenerators = new GeneratorRepresentation(newLines, newParameters,
				newColumnCount);

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
