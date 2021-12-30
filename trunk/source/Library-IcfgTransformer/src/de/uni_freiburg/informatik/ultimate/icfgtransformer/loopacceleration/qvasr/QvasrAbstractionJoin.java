/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class for computing the join of two Qvasr abstractions to form a least upper bound.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public final class QvasrAbstractionJoin {
	private QvasrAbstractionJoin() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Join two given Qvasr abstractions (S_1, V_1) and (S_2, V_2) such that they form a best overapproximation.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param abstractionOne
	 *            {@link QvasrAbstraction} (S_1, V_1)
	 * @param abstractionTwo
	 *            {@link QvasrAbstraction} (S_2, V_2)
	 * @return A joined {@link QvasrAbstraction}
	 */
	public static QvasrAbstraction join(final ManagedScript script, final QvasrAbstraction abstractionOne,
			final QvasrAbstraction abstractionTwo) {

		final Integer concreteDimensionOne = abstractionOne.getQvasr().getConcreteDimension();
		final Integer concreteDimensionTwo = abstractionTwo.getQvasr().getConcreteDimension();

		if (!concreteDimensionOne.equals(concreteDimensionTwo)) {
			throw new UnsupportedOperationException();
		}

		/*
		 * Get coherence classes.
		 */
		final Set<Set<Integer>> abstractionOneCoherenceClasses = getCoherenceClasses(abstractionOne);
		final Set<Set<Integer>> abstractionTwoCoherenceClasses = getCoherenceClasses(abstractionTwo);

		for (final Set<Integer> coherenceClassOne : abstractionOneCoherenceClasses) {

			final Rational[][] coherenceIdentityMatrixOne =
					QvasrUtils.getCoherenceIdentityMatrix(coherenceClassOne, concreteDimensionOne);
			final Rational[][] coherenceIdentitySimulationMatrixOne = QvasrUtils
					.rationalMatrixMultiplication(coherenceIdentityMatrixOne, abstractionOne.getSimulationMatrix());

			for (final Set<Integer> coherenceClassTwo : abstractionTwoCoherenceClasses) {

				final Rational[][] coherenceIdentityMatrixTwo =
						QvasrUtils.getCoherenceIdentityMatrix(coherenceClassTwo, concreteDimensionTwo);

				final Rational[][] coherenceIdentitySimulationMatrixTwo = QvasrUtils
						.rationalMatrixMultiplication(coherenceIdentityMatrixTwo, abstractionTwo.getSimulationMatrix());
				final Pair<Rational[][], Rational[][]> pushedOut =
						pushout(script, coherenceIdentitySimulationMatrixOne, coherenceIdentitySimulationMatrixTwo);
			}
		}
		return null;
	}

	/**
	 * Compute two vectors t_1 and t_2 for two qvasr abstractions (S_1, V_1), (S_2, V_2) such that t_1*S_1 = t_2*S_2
	 *
	 * @param script
	 * @param abstractionOne
	 * @param abstractionTwo
	 * @return
	 */
	private static Pair<Rational[][], Rational[][]> pushout(final ManagedScript script,
			final Rational[][] abstractionOne, final Rational[][] abstractionTwo) {

		final Map<Integer, TermVariable> columnToVar = new HashMap<>();
		final Map<TermVariable, Integer> varToColumnOne = new HashMap<>();
		final Map<TermVariable, Integer> varToColumnTwo = new HashMap<>();

		final Term[] newVarsOne = new Term[abstractionOne[0].length];
		final Term[] newVarsTwo = new Term[abstractionTwo[0].length];
		Integer colCnt = 0;
		for (int i = 0; i < abstractionOne[0].length; i++) {
			final TermVariable newVar =
					script.constructFreshTermVariable("t", SmtSortUtils.getRealSort(script.getScript()));
			newVarsOne[i] = newVar;
			columnToVar.put(colCnt, newVar);
			varToColumnOne.put(newVar, i);
			colCnt++;
		}
		for (int i = 0; i < abstractionTwo[0].length; i++) {
			final TermVariable newVar =
					script.constructFreshTermVariable("t", SmtSortUtils.getRealSort(script.getScript()));
			newVarsTwo[i] = newVar;
			columnToVar.put(colCnt, newVar);
			varToColumnTwo.put(newVar, i);
			colCnt++;
		}
		Term[][] lhs = QvasrUtils.vectorMatrixMultiplicationWithVariables(script, newVarsOne, abstractionOne);
		Term[][] rhs = QvasrUtils.vectorMatrixMultiplicationWithVariables(script, newVarsTwo, abstractionTwo);

		lhs = termMatrixRemoveVariables(script, lhs, varToColumnOne);
		rhs = termMatrixRemoveVariables(script, rhs, varToColumnTwo);
		rhs = addColumnTerm(rhs, script.getScript().decimal("0"));
		final Term[][] joinedMatrix = joinTermMatricesVertically(lhs, changeTermMatrixEntrySign(script, rhs));
		Rational[][] vectorBasis = QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(script, joinedMatrix);
		vectorBasis = removeLastColumnRational(vectorBasis);
		final Pair<Rational[][], Rational[][]> splitVectorBase =
				splitRationalMatricesVertically(vectorBasis, lhs[0].length);
		final Rational[][] lhsRational = splitVectorBase.getFirst();
		final Rational[][] rhsRational = splitVectorBase.getSecond();
		return null;
	}

	/**
	 * Function to turn the sign of each entry in a given {@link Rational} matrix.
	 *
	 * @param matrix
	 *            A {@link Rational} matrix.
	 * @return A rational matrix with entries whose signs are inverted.
	 */
	public static Rational[][] changeRationalMatrixEntrySign(Rational[][] matrix) {
		final Rational[][] changedSignMatrix = new Rational[matrix.length][matrix[0].length];
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				changedSignMatrix[i][j] = matrix[i][j].negate();
			}
		}
		return changedSignMatrix;
	}

	/**
	 * Function to turn the sign of each entry in a given {@link Rational} matrix.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param matrix
	 *            A {@link Rational} matrix.
	 * @return A rational matrix with entries whose signs are inverted.
	 */
	public static Term[][] changeTermMatrixEntrySign(ManagedScript script, Term[][] matrix) {
		final Term[][] changedSignMatrix = new Term[matrix.length][matrix[0].length];
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				changedSignMatrix[i][j] = SmtUtils.neg(script.getScript(), matrix[i][j]);
			}
		}
		return changedSignMatrix;
	}

	/**
	 * Creates a joined Matrix by vertically connecting two matrices. The matrices are required to have the same amount
	 * of rows.
	 *
	 * @param leftSide
	 *            Left hand side of the matrix.
	 * @param rightSide
	 *            Right hand side of the matrix.
	 * @return A vertically joined matrix.
	 */
	public static Term[][] joinTermMatricesVertically(final Term[][] leftSide, final Term[][] rightSide) {
		if (leftSide.length != rightSide.length) {
			return new Term[0][0];
		}
		final Term[][] joinedMatrix = new Term[leftSide.length][leftSide[0].length + rightSide[0].length];
		for (int i = 0; i < leftSide.length; i++) {
			int cnt = 0;
			for (int j = 0; j < leftSide[0].length; j++) {
				joinedMatrix[i][cnt] = leftSide[i][j];
				cnt++;
			}
			for (int k = 0; k < rightSide[0].length; k++) {
				joinedMatrix[i][cnt] = rightSide[i][k];
				cnt++;
			}
		}
		return joinedMatrix;
	}

	/**
	 * Splits a given {@link Rational} matrix vertically along the splitPoint.
	 *
	 * @param matrix
	 *            A still conjoined {@link Rational} matrix.
	 * @param splitPoint
	 *            The Point where the matrix will be split in two.
	 * @return A pair of the left half and the right half of the original matrix.
	 */
	public static Pair<Rational[][], Rational[][]> splitRationalMatricesVertically(final Rational[][] matrix,
			final int splitPoint) {
		final Rational[][] leftSide = new Rational[matrix.length][splitPoint];
		final Rational[][] rightSide = new Rational[matrix.length][splitPoint];

		for (int i = 0; i < matrix.length; i++) {
			leftSide[i] = Arrays.copyOfRange(matrix[i], 0, splitPoint);
			rightSide[i] = Arrays.copyOfRange(matrix[i], splitPoint, matrix[0].length);
		}
		return new Pair<>(leftSide, rightSide);
	}

	/**
	 * Creates a joined Matrix by vertically connecting two matrices. The matrices are required to have the same amount
	 * of rows.
	 *
	 * @param leftSide
	 *            Left hand side of the matrix.
	 * @param rightSide
	 *            Right hand side of the matrix.
	 * @return A vertically joined matrix.
	 */
	public static Rational[][] joinRationalMatricesVertically(final Rational[][] leftSide,
			final Rational[][] rightSide) {
		if (leftSide.length != rightSide.length) {
			return new Rational[0][0];
		}
		final Rational[][] joinedMatrix = new Rational[leftSide.length][leftSide[0].length + rightSide[0].length];
		for (int i = 0; i < leftSide.length; i++) {
			int cnt = 0;
			for (int j = 0; j < leftSide[0].length; j++) {
				joinedMatrix[i][cnt] = leftSide[i][j];
				cnt++;
			}
			for (int k = 0; k < rightSide[0].length; k++) {
				joinedMatrix[i][cnt] = rightSide[i][k];
				cnt++;
			}
		}
		return joinedMatrix;
	}

	/**
	 * Add a new column of value newColumnValue to a given term matrix.
	 *
	 * @param matrix
	 *            The matrix that will be expanded.
	 * @param newColumnValue
	 *            The appended columns new value.
	 * @return A matrix with a new column.
	 */
	public static Term[][] addColumnTerm(final Term[][] matrix, Term newColumnValue) {
		final Term[][] result = new Term[matrix.length][matrix[0].length + 1];
		for (int i = 0; i < matrix.length; i++) {
			result[i] = Arrays.copyOf(matrix[i], matrix[i].length + 1);
			result[i][matrix[i].length] = newColumnValue;
		}
		return result;
	}

	/**
	 * Remove the last column in a {@link Rational} matrix.
	 *
	 * @param matrix
	 *            The matrix that will be expanded.
	 * @param newColumnValue
	 *            The appended columns new value.
	 * @return A matrix with a new column.
	 */
	public static Rational[][] removeLastColumnRational(final Rational[][] matrix) {
		final Rational[][] result = new Rational[matrix.length][matrix[0].length - 1];
		for (int i = 0; i < matrix.length; i++) {
			result[i] = Arrays.copyOf(matrix[i], matrix[i].length - 1);
		}
		return result;
	}

	/**
	 * Removes termvariables from a matrix and only leaves their coefficient.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param termMatrix
	 *            A matrix containing termvariables.
	 * @param varToColumn
	 *            A Map that maps termvariables to their corresponding column in the original matrix.
	 * @return A term matrix without termsvariables
	 */
	private static Term[][] termMatrixRemoveVariables(final ManagedScript script, final Term[][] termMatrix,
			final Map<TermVariable, Integer> varToColumn) {

		final Set<TermVariable> tvs = varToColumn.keySet();
		final int newMatrixLength = tvs.size();
		final Term[][] matrixNoVars = new Term[termMatrix.length][newMatrixLength];
		for (int i = 0; i < termMatrix.length; i++) {
			for (int j = 0; j < termMatrix[0].length; j++) {
				final Term equation = termMatrix[i][j];
				if (QvasrUtils.isApplicationTerm(equation)) {
					for (final Term var : tvs) {
						final Set<TermVariable> zeroTvs = new HashSet<>(tvs);
						zeroTvs.remove(var);
						final HashMap<Term, Term> subMap = new HashMap<>();
						subMap.put(var, script.getScript().decimal("1.0"));
						for (final Term zeroTv : zeroTvs) {
							subMap.put(zeroTv, script.getScript().decimal("0"));
						}
						final Term constTerm = Substitution.apply(script, subMap, equation);
						matrixNoVars[i][varToColumn.get(var)] = constTerm;
					}
				}
			}
		}
		return matrixNoVars;
	}

	/**
	 * Converts a matrix of termvariables to a rational matrix in expanded matrix form that can be used for gaussian
	 * elimination.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param termMatrix
	 *            A matrix containing logical {@link Term}
	 * @param varToColumn
	 *            A Map that maps termvariables to their corresponding column in the original matrix.
	 * @return A rational matrix without terms.
	 */
	private static Rational[][] termMatrixToRational(final ManagedScript script, final Term[][] termMatrix,
			final Map<TermVariable, Integer> varToColumn) {
		final Set<TermVariable> tvs = varToColumn.keySet();
		final int newMatrixLength = tvs.size();
		final Rational[][] rationalMatrix = new Rational[termMatrix.length][newMatrixLength];
		for (int i = 0; i < termMatrix.length; i++) {
			for (int j = 0; j < termMatrix[0].length; j++) {
				final Term equation = termMatrix[i][j];
				if (QvasrUtils.isApplicationTerm(equation)) {
					for (final Term var : tvs) {
						final Set<TermVariable> zeroTvs = new HashSet<>(tvs);
						zeroTvs.remove(var);
						final HashMap<Term, Term> subMap = new HashMap<>();
						subMap.put(var, script.getScript().decimal("1.0"));
						for (final Term zeroTv : zeroTvs) {
							subMap.put(zeroTv, script.getScript().decimal("0"));
						}
						final ConstantTerm constTerm = (ConstantTerm) Substitution.apply(script, subMap, equation);
						final Rational entryAsRational = (Rational) constTerm.getValue();
						rationalMatrix[i][varToColumn.get(var)] = entryAsRational;
					}
				}
			}
		}
		return rationalMatrix;
	}

	/**
	 * Get coherence classes of a given Qvasr abstraction. A coherence class is a set of rows i,j, where r_i = r_j in
	 * the reset vector of the abstraction's qvasr.
	 *
	 * @param qvasrAbstraction
	 * @return
	 */
	private static Set<Set<Integer>> getCoherenceClasses(final QvasrAbstraction qvasrAbstraction) {
		final Qvasr qvasr = qvasrAbstraction.getQvasr();
		final Set<Set<Integer>> coherenceClasses = new HashSet<>();
		for (final Pair<Rational[], Rational[]> transformer : qvasr.getQvasrTransformer()) {
			final Rational[] resetVector = transformer.getFirst();
			for (int i = 0; i < resetVector.length; i++) {
				final Set<Integer> coherenceClass = new HashSet<>();
				coherenceClass.add(i);
				for (int j = 0; j < resetVector.length; j++) {
					if (i != j && resetVector[i] == resetVector[j]) {
						coherenceClass.add(j);
					}
				}
				coherenceClasses.add(coherenceClass);
			}
		}
		return coherenceClasses;
	}

}
