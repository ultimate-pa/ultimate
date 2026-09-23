/*
 * Copyright (C) 2026 Max Lehr
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * State used in {@link CongruenceDomain}
 *
 * @author Max Lehr
 *
 */
public class CongruenceState implements IAbstractState<CongruenceState> {
	public static final CongruenceState TOP = new CongruenceState(Map.of(), ConstraintRepresentation.getEmpty(0));

	/**
	 * Map of numerical variable (ints and reals) names to unique indexes used in the internal representations of
	 * {@link ConstraintRepresentation} and {@link GeneratorRepresentation}.
	 */
	private final Map<Term, Integer> mVarToIndex;

	/**
	 * Representation of the state as constraints in the form of equalities and congruences.
	 */
	private ConstraintRepresentation mConstraints;
	/**
	 * Representation of the state as vectors generating the valid variable assignments.
	 */
	private GeneratorRepresentation mGenerators;

	private Boolean mIsBottom = null;

	public CongruenceState(final Map<Term, Integer> varToIndex, final ConstraintRepresentation constraints) {
		mVarToIndex = varToIndex;
		mConstraints = constraints;
		mGenerators = null;
	}

	public CongruenceState(final Map<Term, Integer> varToIndex, final GeneratorRepresentation generators) {
		mVarToIndex = varToIndex;
		mConstraints = null;
		mGenerators = generators;
	}

	public ConstraintRepresentation getConstraintRepresentation() {
		if (mConstraints == null) {
			mConstraints = mGenerators.computeConstraintRepresentation();
		}
		return mConstraints;
	}

	public GeneratorRepresentation getGeneratorRepresentation() {
		if (mGenerators == null) {
			mGenerators = mConstraints.computeGeneratorRepresentation();
		}
		return mGenerators;
	}

	public Map<Term, Integer> getVarToIndex() {
		return mVarToIndex;
	}

	/**
	 * Returns the inverse mapping of mVarToIndex.
	 */
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
		final List<RationalVector> equalities = constraints.getEqualities();
		final List<RationalVector> congruences = constraints.getCongruences();

		final Map<Integer, Term> indexToVar = getIndexToVar();

		final StringBuilder constraintsString = new StringBuilder();

		for (final RationalVector equality : equalities) {
			final BigInteger commonDenominator = CongruenceUtil.getCommonDenominator(equality);
			final RationalVector wholeEquality = equality.multiply(commonDenominator);
			final String[] vectorStrings = getVectorStrings(wholeEquality, indexToVar);
			final String equalityString = vectorStrings[0] + " = " + vectorStrings[1];
			constraintsString.append(equalityString).append(";\n");
		}

		for (final RationalVector congruence : congruences) {
			final BigInteger commonDenominator = CongruenceUtil.getCommonDenominator(congruence);
			final RationalVector wholeCongruence = congruence.multiply(commonDenominator);
			final String[] vectorStrings = getVectorStrings(wholeCongruence, indexToVar);
			final String congruenceString = vectorStrings[0] + " ≡" + commonDenominator + " " + vectorStrings[1];
			constraintsString.append(congruenceString).append(";\n");
		}

		return "CongruenceState [mVarToIndex=" + mVarToIndex + ", mConstraints= \n"
				+ constraintsString.append("]").toString();
	}

	/**
	 * Takes a vector containing rational coefficients and a map from the indexes of the vector to variables, together
	 * modeling a polynomial p. Returns an array containing two strings, each representing one side of an equality
	 * equivalent to p=0.
	 */
	private static String[] getVectorStrings(final RationalVector vector, final Map<Integer, Term> indexToVar) {
		String resultString = "0";
		final Set<String> summands = new HashSet<>();
		for (int i = 0; i < vector.getLength(); i++) {
			final Rational rationalFactor = vector.get(i);

			if (rationalFactor.equals(Rational.ZERO)) {
				continue;
			}
			final BigInteger factor = rationalFactor.numerator();

			String term;
			if (i == 0) {
				resultString = factor.negate().toString();
			} else {
				final Term var = indexToVar.get(i);
				if (factor.equals(BigInteger.ONE)) {
					term = var.toString();
				} else {
					term = factor + " * " + var;
				}
				summands.add(term);
			}
		}

		final String[] summandsArray = summands.toArray(String[]::new);

		if (summandsArray.length == 0) {
			return new String[] { "0", resultString };
		}

		StringBuilder sum = new StringBuilder();
		for (final String element : summandsArray) {
			sum.append(" + ").append(element);
		}
		sum = sum.delete(0, 2);
		return new String[] { sum.toString(), resultString };
	}

	@Override
	public Term toTerm(final Script script) {

		if (isBottom()) {
			return script.term("false");
		}

		final ConstraintRepresentation constraints = getConstraintRepresentation();
		final List<RationalVector> equalities = constraints.getEqualities();
		final List<RationalVector> congruences = constraints.getCongruences();

		final Map<Integer, Term> indexToVar = getIndexToVar();

		final Set<Term> terms = new HashSet<>();

		for (final RationalVector equality : equalities) {
			final BigInteger commonDenominator = CongruenceUtil.getCommonDenominator(equality);
			final RationalVector wholeEquality = equality.multiply(commonDenominator);
			final Term sum = getSumTerm(wholeEquality, indexToVar, script);
			final Term equalityTerm =
					SmtUtils.binaryEquality(script, sum, SmtUtils.constructIntValue(script, BigInteger.ZERO));
			terms.add(equalityTerm);
		}

		for (final RationalVector congruence : congruences) {
			final BigInteger commonDenominator = CongruenceUtil.getCommonDenominator(congruence);
			final RationalVector wholeCongruence = congruence.multiply(commonDenominator);
			final Term sum = getSumTerm(wholeCongruence, indexToVar, script);
			final Term modTerm = SmtUtils.constructIntValue(script, commonDenominator);
			final Term modSum = SmtUtils.mod(script, sum, modTerm);
			final Term congruenceTerm =
					SmtUtils.binaryEquality(script, modSum, SmtUtils.constructIntValue(script, BigInteger.ZERO));
			terms.add(congruenceTerm);
		}

		return SmtUtils.and(script, terms);
	}

	/**
	 * Takes a vector containing rational coefficients and a map from the indexes of the vector to variables, together
	 * modeling a polynomial. Returns a term equivalent to this polynomial.
	 */
	private static Term getSumTerm(final RationalVector vector, final Map<Integer, Term> indexToVar,
			final Script script) {

		final Set<Term> summands = new HashSet<>();
		for (int i = 0; i < vector.getLength(); i++) {
			final Rational rationalFactor = vector.get(i);

			if (rationalFactor.equals(Rational.ZERO)) {
				continue;
			}

			final BigInteger factor = rationalFactor.numerator();

			Term term;
			if (i == 0) {
				term = SmtUtils.constructIntValue(script, factor);
			} else {
				final Term var = indexToVar.get(i);
				term = SmtUtils.mul(script, Rational.valueOf(factor, BigInteger.ONE), var);
			}
			summands.add(term);
		}

		final Term[] summandsArray = summands.toArray(Term[]::new);

		return SmtUtils.sum(script, SmtSortUtils.getIntSort(script), summandsArray);
	}

	/**
	 * Returns an equivalent CongruenceState that uses newVarToIndex as its mapping from variables to indexes.
	 */
	private CongruenceState getReorderedForm(final Map<Term, Integer> newVarToIndex) {
		// Compute the required lengths for the vectors
		// +1 for the constant in the first place
		final int newColumnCount = newVarToIndex.size() + 1;

		// Compute the reorder map for the variables
		final Map<Integer, Integer> reorderMap = CongruenceUtil.getReorderForMaps(mVarToIndex, newVarToIndex);
		// Add the mapping for the constant factor
		reorderMap.put(0, 0);

		// Compute the reordered forms of the constraints
		final ConstraintRepresentation constraints = getConstraintRepresentation();
		final ConstraintRepresentation reorderedConstraints = constraints.getReorderedForm(reorderMap, newColumnCount);

		return new CongruenceState(newVarToIndex, reorderedConstraints);
	}

	@Override
	public CongruenceState join(final CongruenceState other) {
		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}

		// Compute the new VarToIndex
		final Map<Term, Integer> selfVarToIndex = getVarToIndex();
		final Map<Term, Integer> otherVarToIndex = other.getVarToIndex();
		final Map<Term, Integer> newVarToIndex = CongruenceUtil.mergeMaps(selfVarToIndex, otherVarToIndex);

		final CongruenceState selfReorderedForm = getReorderedForm(newVarToIndex);
		final CongruenceState otherReorderedForm = other.getReorderedForm(newVarToIndex);

		final GeneratorRepresentation selfReorderedGenerators = selfReorderedForm.getGeneratorRepresentation();
		final GeneratorRepresentation otherReorderedGenerators = otherReorderedForm.getGeneratorRepresentation();

		// Combine the generators
		final List<RationalVector> newLines = selfReorderedGenerators.getLines();
		newLines.addAll(otherReorderedGenerators.getLines());

		final List<RationalVector> newParameters = selfReorderedGenerators.getParameters();
		newParameters.addAll(otherReorderedGenerators.getParameters());

		final GeneratorRepresentation newGenerators =
				new GeneratorRepresentation(newLines, newParameters, selfReorderedGenerators.getVectorLength());

		return new CongruenceState(newVarToIndex, newGenerators);
	}

	@Override
	public CongruenceState widen(final CongruenceState other) {

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
		final GeneratorRepresentation lowerGenerators = lower.getGeneratorRepresentation();

		final ConstraintRepresentation upperConstraints = upper.getConstraintRepresentation();
		upperConstraints.stronglyMinimize();

		if (lowerGenerators.isUnsat() || lowerConstraints.getDim() < upperConstraints.getDim()) {
			return upper;
		}

		// CS := {γ ∈ C2 | ∃β ∈ C1 . β ⇑ γ}

		final List<RationalVector> lowerVectors = new ArrayList<>(lowerConstraints.getEqualities());
		lowerVectors.addAll(lowerConstraints.getCongruences());

		final List<RationalVector> newEqualities = new ArrayList<>();
		for (final RationalVector equality : upperConstraints.getEqualities()) {
			for (final RationalVector lowerVector : lowerVectors) {
				if (CongruenceUtil.isEqualsInLastNonZero(equality, lowerVector)) {
					newEqualities.add(equality);
				}
			}
		}

		final List<RationalVector> newCongruences = new ArrayList<>();
		for (final RationalVector congruence : upperConstraints.getCongruences()) {
			for (final RationalVector lowerVector : lowerVectors) {
				if (CongruenceUtil.isEqualsInLastNonZero(congruence, lowerVector)) {
					newCongruences.add(congruence);
				}
			}
		}

		final ConstraintRepresentation newConstraints =
				new ConstraintRepresentation(newEqualities, newCongruences, upperConstraints.getVectorLength());

		return new CongruenceState(newVarToIndex, newConstraints);
	}

	@Override
	public boolean isBottom() {
		if (mIsBottom != null) {
			return mIsBottom;
		}
		final GeneratorRepresentation generators = getGeneratorRepresentation();
		mIsBottom = generators.isUnsat();
		return mIsBottom;
	}
}
