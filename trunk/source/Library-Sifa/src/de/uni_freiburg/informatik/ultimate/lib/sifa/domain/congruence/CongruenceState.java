package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
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
	public String toString() {
		final ConstraintRepresentation constraints = getConstraintRepresentation();
		final List<MatrixQ128> equalities = constraints.getEqualities();
		final List<MatrixQ128> congruences = constraints.getCongruences();

		final Map<Integer, Term> indexToVar = getIndexToVar();

		final StringBuilder constraintsString = new StringBuilder();

		for (final MatrixQ128 equality : equalities) {
			final long commonDenominator = CongruenceUtil.getCommonDenominator(equality);
			final MatrixQ128 wholeEquality = equality.multiply(commonDenominator);
			final String[] vectorStrings = CongruenceUtil.getVectorStrings(wholeEquality, indexToVar);
			final String equalityString = vectorStrings[0] + " = " + vectorStrings[1];
			constraintsString.append(equalityString).append(";\n");
		}

		for (final MatrixQ128 congruence : congruences) {
			final long commonDenominator = CongruenceUtil.getCommonDenominator(congruence);
			final MatrixQ128 wholeCongruence = congruence.multiply(commonDenominator);
			final String[] vectorStrings = CongruenceUtil.getVectorStrings(wholeCongruence, indexToVar);
			final String congruenceString = vectorStrings[0] + " ≡" + commonDenominator + " " + vectorStrings[1];
			constraintsString.append(congruenceString).append(";\n");
		}

		return "CongruenceState [mVarToIndex=" + mVarToIndex + ", mConstraints= \n"
				+ constraintsString.append("]").toString();
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

	public CongruenceState getReorderedForm(final Map<Term, Integer> newVarToIndex) {
		// Compute the required lengths for the vectors.
		// +1 for the constant in the first place
		final int newColumnCount = newVarToIndex.size() + 1;

		// Compute the reordered forms of the generators
		final Map<Integer, Integer> reorderMap = CongruenceUtil.getReorderForMaps(mVarToIndex, newVarToIndex);
		reorderMap.put(0, 0);
		final GeneratorRepresentation generators = getGeneratorRepresentation();
		final GeneratorRepresentation reorderedGenerators = generators.getReorderedForm(reorderMap, newColumnCount);

		return new CongruenceState(newVarToIndex, reorderedGenerators);
	}

	@Override
	public CongruenceState join(final CongruenceState other) {
		// Compute the new VarToIndex
		final Map<Term, Integer> selfVarToIndex = getVarToIndex();
		final Map<Term, Integer> otherVarToIndex = other.getVarToIndex();
		final Map<Term, Integer> newVarToIndex = CongruenceUtil.mergeMaps(selfVarToIndex, otherVarToIndex);

		final CongruenceState selfReorderedForm = getReorderedForm(newVarToIndex);
		final CongruenceState otherReorderedForm = other.getReorderedForm(newVarToIndex);

		final GeneratorRepresentation selfReorderedGenerators = selfReorderedForm.getGeneratorRepresentation();
		final GeneratorRepresentation otherReorderedGenerators = otherReorderedForm.getGeneratorRepresentation();

		// Combine the generators
		final List<MatrixQ128> newLines = selfReorderedGenerators.getLines();
		newLines.addAll(otherReorderedGenerators.getLines());

		final List<MatrixQ128> newParameters = selfReorderedGenerators.getParameters();
		newParameters.addAll(otherReorderedGenerators.getParameters());

		final GeneratorRepresentation newGenerators = new GeneratorRepresentation(newLines, newParameters,
				selfReorderedGenerators.getVectorLength());

		return new CongruenceState(newVarToIndex, newGenerators);
	}

	@Override
	public CongruenceState widen(final CongruenceState other) {

		final var sth = 0;

		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}

		final CongruenceState upper = join(other);
		final var newVarToIndex = upper.getVarToIndex();
		final CongruenceState lower = other.getReorderedForm(newVarToIndex);

		final ConstraintRepresentation lowerConstraints = lower.getConstraintRepresentation();
		lowerConstraints.minimize();

		final ConstraintRepresentation upperConstraints = upper.getConstraintRepresentation();
		upperConstraints.stronglyMinimize();

		if (lowerConstraints.isUnsat() || lowerConstraints.getDim() < upperConstraints.getDim()) {
			return upper;
		}

		// CS := {γ ∈ C2 | ∃β ∈ C1 . β ⇑ γ}

		final List<MatrixQ128> lowerVectors = new ArrayList<>(lowerConstraints.getEqualities());
		lowerVectors.addAll(lowerConstraints.getCongruences());

		final List<MatrixQ128> newEqualities = new ArrayList<>();
		for (final MatrixQ128 equality : upperConstraints.getEqualities()) {
			for (final MatrixQ128 lowerVector : lowerVectors) {
				if (CongruenceUtil.isEqualsInLastNonZero(equality, lowerVector)) {
					newEqualities.add(equality);
				}
			}
		}

		final List<MatrixQ128> newCongruences = new ArrayList<>();
		for (final MatrixQ128 congruence : upperConstraints.getCongruences()) {
			for (final MatrixQ128 lowerVector : lowerVectors) {
				if (CongruenceUtil.isEqualsInLastNonZero(congruence, lowerVector)) {
					newCongruences.add(congruence);
				}
			}
		}

		final ConstraintRepresentation newConstraints = new ConstraintRepresentation(newEqualities, newCongruences,
				upperConstraints.getVectorLength());
		return new CongruenceState(newVarToIndex, newConstraints);
	}

	@Override
	public boolean isBottom() {
		final ConstraintRepresentation constraints = getConstraintRepresentation();
		return constraints.isUnsat();
	}

}
