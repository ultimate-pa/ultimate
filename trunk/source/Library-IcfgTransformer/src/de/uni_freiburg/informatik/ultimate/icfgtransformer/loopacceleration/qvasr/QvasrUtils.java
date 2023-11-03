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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs.IntVasrsAbstraction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs.QvasrsAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * A collection of useful functions needed in Q-Vasr-abstraction, and matrix operations.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */
public final class QvasrUtils {
	private QvasrUtils() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Split a {@link Term} in DNF into its conjuncts.
	 *
	 * @param term
	 *            A term in disjunctive normal form.
	 * @return A list of terms representing each disjunct.
	 */
	public static Set<Term> splitDisjunction(final Term term) {
		final Set<Term> result = new HashSet<>();
		final ApplicationTerm dnfAppTerm = (ApplicationTerm) term;
		if (!"or".equals(dnfAppTerm.getFunction().getName())) {
			result.add(term);
		} else {
			result.addAll(Arrays.asList(dnfAppTerm.getParameters()));
		}
		return result;
	}

	public static Set<Term> checkDisjoint(final Set<Term> disjuncts, final ManagedScript script,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique) {
		final Deque<Term> checkStack = new HashDeque<>();
		final Set<Term> disjointSet = new HashSet<>();
		checkStack.addAll(disjuncts);
		while (!checkStack.isEmpty()) {
			final Term toBeChecked = checkStack.pop();
			boolean isSat = false;
			for (final Term conjunct : checkStack) {
				if (SmtUtils.checkSatTerm(script.getScript(),
						SmtUtils.and(script.getScript(), toBeChecked, conjunct)) == LBool.SAT) {
					checkStack.add(SmtUtils.simplify(script, SmtUtils.or(script.getScript(), toBeChecked, conjunct),
							services, simplificationTechnique));
					isSat = true;
					break;
				}
			}
			if (!isSat) {
				disjointSet.add(toBeChecked);
			}
		}
		return disjointSet;
	}

	/**
	 * Get a matrix k*d, with entries corresponding to coherence classes.
	 *
	 * @param coherenceClass
	 *            A coherence class.
	 * @param d
	 *            concrete dimension of a {@link Qvasr}
	 * @return An identitiy matrix with 1s only in coherence class corresponding columns.
	 */
	public static Rational[][] getCoherenceIdentityMatrix(final Set<Integer> coherenceClass, final int d) {
		final Rational[][] coherenceIdentityMatrix = new Rational[coherenceClass.size()][d];
		for (int i = 0; i < coherenceClass.size(); i++) {
			for (int j = 0; j < d; j++) {
				coherenceIdentityMatrix[i][j] = Rational.ZERO;
			}
		}
		int k = 0;
		for (final Integer classLine : coherenceClass) {
			coherenceIdentityMatrix[k][classLine] = Rational.ONE;
			k++;
		}
		return coherenceIdentityMatrix;
	}

	/**
	 * Construct a matrix of equal dimension where the diagonal entries are 1s and the rest 0s.
	 *
	 * @param dimension
	 *            The dimension of the identity matrix.
	 * @return An identity matrix of given dimension.
	 */
	public static Rational[][] getIdentityMatrix(final int dimension) {
		final Rational[][] identityMatrix = new Rational[dimension][dimension];
		for (int i = 0; i < dimension; i++) {
			for (int j = 0; j < dimension; j++) {
				if (i == j) {
					identityMatrix[i][j] = Rational.ONE;
				} else {
					identityMatrix[i][j] = Rational.ZERO;
				}
			}
		}
		return identityMatrix;
	}

	/**
	 * Standard vector matrix multiplication of a vector containing {@link Term} and a rational matrix. They are not
	 * associative.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param vector
	 *            A vector with {@link Term}
	 *
	 * @param matrixTwo
	 *            A {@link Rational} matrix.
	 * @return The product of both.
	 */
	public static Term[][] vectorMatrixMultiplicationWithVariables(final ManagedScript script, final Term[] vector,
			final Rational[][] matrixTwo) {
		final int vectorLength = vector.length;
		final int rowMatrixTwo = matrixTwo.length;
		if (vectorLength != rowMatrixTwo) {
			throw new UnsupportedOperationException();
		}
		final int colMatrixTwo = matrixTwo[0].length;
		final Term[][] resultMatrix = new Term[1][colMatrixTwo];
		for (int i = 0; i < colMatrixTwo; i++) {
			resultMatrix[0][i] = script.getScript().decimal("0");

		}
		for (int j = 0; j < colMatrixTwo; j++) {
			Term sum = script.getScript().decimal("0");
			for (int k = 0; k < rowMatrixTwo; k++) {
				final Term mult = SmtUtils.mul(script.getScript(), "*", vector[k],
						matrixTwo[k][j].toTerm(SmtSortUtils.getRealSort(script)));
				sum = SmtUtils.sum(script.getScript(), "+", sum, mult);
				resultMatrix[0][j] = sum;
			}
		}
		return resultMatrix;
	}

	/**
	 * Standard vector matrix multiplication of a vector containing {@link Term} and a rational matrix. They are not
	 * associative.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param vector
	 *            A vector with {@link Term}
	 *
	 * @param matrixTwo
	 *            A {@link Rational} matrix.
	 * @return The product of both.
	 */
	public static Term[][] matrixVectorMultiplicationWithVariables(final ManagedScript script,
			final Integer[][] matrixTwo, final Term[][] vector) {
		final int vectorLength = vector.length;
		final int colMatrixTwo = matrixTwo[0].length;
		assert vectorLength == colMatrixTwo;
		final int rowMatrixTwo = matrixTwo.length;

		final Term[][] resultMatrix = new Term[rowMatrixTwo][1];
		for (int i = 0; i < rowMatrixTwo; i++) {
			resultMatrix[i][0] = script.getScript().numeral("0");

		}
		for (int j = 0; j < rowMatrixTwo; j++) {
			Term sum = script.getScript().numeral("0");
			for (int k = 0; k < colMatrixTwo; k++) {
				final Term mult = SmtUtils.mul(script.getScript(), "*", vector[k][0],
						script.getScript().numeral(matrixTwo[j][k].toString()));
				sum = SmtUtils.sum(script.getScript(), "+", sum, mult);
				resultMatrix[j][0] = sum;
			}
		}
		return resultMatrix;
	}

	/**
	 * Checks for equivalence of two terms.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param firstEntry
	 *            A {@link Term}
	 * @param secondEntry
	 *            A {@link Term}
	 * @return true iff they are equivalent, else false.
	 */
	public static boolean checkTermEquiv(final ManagedScript script, final Term firstEntry, final Term secondEntry) {
		return SmtUtils.areFormulasEquivalent(firstEntry, secondEntry, script.getScript());
	}

	/**
	 * Check whether a given {@link Term} is an {@link ApplicationTerm}
	 *
	 * @param term
	 *            A term to be checked.
	 * @return True iff the term is an application term, else false.
	 */
	public static boolean isApplicationTerm(final Term term) {
		return term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0;
	}

	/**
	 * Construct a new {@link UnmodifiableTransFormula} from a term. This term is part of the DNF of the original
	 * formula. There eligible.
	 *
	 * @param origin
	 *            Original {@link UnmodifiableTransFormula}
	 * @param term
	 *            Disjunct term of the new formula.
	 * @param managedScript
	 *            A {@link ManagedScript}
	 * @return A new {@link UnmodifiableTransFormula}
	 */
	public static UnmodifiableTransFormula buildFormula(final UnmodifiableTransFormula origin, final Term term,
			final ManagedScript managedScript) {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(origin.getInVars(), origin.getOutVars(), true, null, true, null, false);
		tfb.setFormula(term);
		tfb.addAuxVarsButRenameToFreshCopies(origin.getAuxVars(), managedScript);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Construct a new {@link UnmodifiableTransFormula} from a term. This term is part of the DNF of the original
	 * formula. There eligible.
	 *
	 * @param origin
	 *            Original {@link UnmodifiableTransFormula}
	 * @param term
	 *            Disjunct term of the new formula.
	 * @param managedScript
	 *            A {@link ManagedScript}
	 * @return A new {@link UnmodifiableTransFormula}
	 */
	public static UnmodifiableTransFormula buildFormula(final ManagedScript managedScript, final Term term,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Standard vector matrix multiplication of a {@link Rational} matrix and a {@link Rational} vector. They are not
	 * associative.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param vector
	 *            A vector with {@link Term}
	 *
	 * @param matrix
	 *            A {@link Rational} matrix.
	 * @return The product of both.
	 */
	public static Rational[][] rationalMatrixVectorMultiplication(final Rational[][] matrix, Rational[][] vector) {
		/*
		 * In case the matrix is a vector.
		 */
		if (vector.length == 1) {
			vector = transposeRowToColumnVector(vector);
		}
		final int vectorLength = vector.length;
		final int colMatrix = matrix[0].length;
		if (vectorLength != colMatrix) {
			throw new UnsupportedOperationException();
		}
		final int rowMatrix = matrix.length;
		final Rational[][] resultMatrix = new Rational[rowMatrix][1];
		for (int j = 0; j < rowMatrix; j++) {
			Rational sum = Rational.ZERO;
			for (int k = 0; k < colMatrix; k++) {
				final Rational mult = vector[k][0].mul(matrix[j][k]);
				sum = sum.add(mult);
				resultMatrix[j][0] = sum;
			}
		}
		return resultMatrix;
	}

	/**
	 * Standard matrix multiplication of two rational matrices.
	 *
	 * @param matrixOne
	 *            The first matrix
	 * @param matrixTwo
	 *            The second matrix
	 * @return The product of both matrices.
	 */
	public static Rational[][] rationalMatrixMultiplication(final Rational[][] matrixOne,
			final Rational[][] matrixTwo) {
		final int rowMatrixTwo = matrixTwo.length;
		final int colMatrixOne = matrixOne[0].length;
		if (colMatrixOne != rowMatrixTwo) {
			return new Rational[0][0];
		}
		final int colMatrixTwo = matrixTwo[0].length;
		final int rowMatrixOne = matrixOne.length;
		final Rational[][] resultMatrix = new Rational[rowMatrixOne][colMatrixTwo];
		for (int i = 0; i < rowMatrixOne; i++) {
			for (int j = 0; j < colMatrixTwo; j++) {
				resultMatrix[i][j] = Rational.ZERO;
			}
		}
		for (int i = 0; i < rowMatrixOne; i++) {
			for (int j = 0; j < colMatrixTwo; j++) {
				for (int k = 0; k < colMatrixOne; k++) {
					final Rational mul = matrixOne[i][k].mul(matrixTwo[k][j]);
					final Rational sum = resultMatrix[i][j].add(mul);
					resultMatrix[i][j] = sum;

				}
			}
		}
		return resultMatrix;
	}

	/**
	 * Transpose a rational row vector to a rational column vector.
	 *
	 * @param vector
	 *            A rational vector to be transposed.
	 * @return The transposed vector.
	 */
	public static Rational[][] transposeRowToColumnVector(final Rational[][] vector) {
		final Rational[][] transposedVector = new Rational[vector[0].length][1];
		for (int i = 0; i < vector[0].length; i++) {
			transposedVector[i][0] = vector[0][i];
		}
		return transposedVector;
	}

	/**
	 * Transpose a rational row vector to a rational column vector.
	 *
	 * @param vector
	 *            A rational vector to be transposed.
	 * @return The transposed vector.
	 */
	public static Rational[][] transposeRowToColumnVector(final Rational[] vector) {
		final Rational[][] transposedVector = new Rational[vector.length][1];
		for (int i = 0; i < vector.length; i++) {
			transposedVector[i][0] = vector[i];
		}
		return transposedVector;
	}

	/**
	 * Transpose a rational row vector to a rational column vector.
	 *
	 * @param vector
	 *            A rational vector to be transposed.
	 * @return The transposed vector.
	 */
	public static Term[][] transposeRowToColumnTermVector(final Term[] vector) {
		final Term[][] transposedVector = new Term[vector.length][1];
		for (int i = 0; i < vector.length; i++) {
			transposedVector[i][0] = vector[i];
		}
		return transposedVector;
	}

	/**
	 * Transpose a rational row vector to a rational column vector.
	 *
	 * @param vector
	 *            A rational vector to be transposed.
	 * @return The transposed vector.
	 */
	public static Rational[] transposeColumnToRowVector(final Rational[][] vector) {
		final Rational[] transposedVector = new Rational[vector.length];
		for (int i = 0; i < vector.length; i++) {
			transposedVector[i] = vector[i][0];
		}
		return transposedVector;
	}

	/**
	 * Embed a new variable into a set of subsets, by adding it to each already existing subsets.
	 *
	 * @param inSet
	 *            Already existing set of {@link Term}
	 * @param variable
	 *            A new join.
	 * @return A joined Set.
	 */
	public static Set<Set<Term>> joinSet(final Set<Set<Term>> inSet, final Set<Term> variable) {
		final Set<Set<Term>> joinedSet = new HashSet<>(inSet);
		for (final Set<Term> toBeJoined : inSet) {
			final Set<Term> varJoin = new HashSet<>();
			varJoin.addAll(toBeJoined);
			varJoin.addAll(variable);
			joinedSet.add(varJoin);
		}
		return joinedSet;
	}

	public static BigInteger getLeastCommonMultiple(final QvasrAbstraction qvasrAbstraction) {
		BigInteger gcd = BigInteger.ZERO;
		BigInteger mult = BigInteger.ONE;
		for (int i = 0; i < qvasrAbstraction.getSimulationMatrix().length; i++) {
			for (int j = 0; j < qvasrAbstraction.getSimulationMatrix()[0].length; j++) {
				final Rational rational = qvasrAbstraction.getSimulationMatrix()[i][j];
				if (!rational.isIntegral()) {
					gcd = Rational.gcd(gcd, rational.denominator());
					mult = mult.multiply(rational.denominator());
				}
			}
		}
		for (final Pair<Rational[], Rational[]> transformer : qvasrAbstraction.getVasr().getTransformer()) {
			final Rational[] additionVector = transformer.getSecond();
			for (int k = 0; k < additionVector.length; k++) {
				if (!additionVector[k].isIntegral()) {
					gcd = Rational.gcd(gcd, additionVector[k].denominator());
					mult = mult.multiply(additionVector[k].denominator());
				}
			}
		}
		if (gcd == BigInteger.ZERO) {
			gcd = BigInteger.ONE;
		}
		BigInteger lcm = mult.divide(gcd);
		if (lcm.equals(BigInteger.ONE)) {
			lcm = gcd;
		}
		return lcm;
	}

	/**
	 * Convert a given {@link QvasrAbstraction} consisting of {@link Rational} to an {@link IntvasrAbstraction} by
	 * computing the least common multiple of the simulation matrix and addition vectors, then multiplying the entries
	 * with it. Resulting in an integral vector addition system.
	 *
	 * @param qvasrAbstraction
	 *            The {@link QvasrAbstraction} that will be converted to an {@link IntvasrAbstraction}
	 * @return The converted {@link IntvasrAbstraction}
	 */
	public static IntvasrAbstraction qvasrAbstractionToInt(final QvasrAbstraction qvasrAbstraction) {
		final BigInteger lcm = getLeastCommonMultiple(qvasrAbstraction);
		final Integer[][] integerSimulationMatrix = new Integer[qvasrAbstraction
				.getSimulationMatrix().length][qvasrAbstraction.getSimulationMatrix()[0].length];
		for (int i = 0; i < integerSimulationMatrix.length; i++) {
			for (int j = 0; j < integerSimulationMatrix[0].length; j++) {
				final Rational oldRationalEntry = qvasrAbstraction.getSimulationMatrix()[i][j].mul(lcm);
				assert oldRationalEntry.isIntegral();
				integerSimulationMatrix[i][j] = oldRationalEntry.numerator().intValue();
			}
		}
		final Intvasr intVasr = new Intvasr();
		for (final Pair<Rational[], Rational[]> transformer : qvasrAbstraction.getVasr().getTransformer()) {
			final Integer[] resetVectorInt = new Integer[transformer.getFirst().length];
			final Integer[] additionVectorInt = new Integer[transformer.getFirst().length];
			for (int i = 0; i < transformer.getFirst().length; i++) {
				assert transformer.getFirst()[i].isIntegral();
				resetVectorInt[i] = transformer.getFirst()[i].numerator().intValue();
				final Rational oldRationalEntry = transformer.getSecond()[i].mul(lcm);
				assert oldRationalEntry.isIntegral();
				additionVectorInt[i] = oldRationalEntry.numerator().intValue();
			}
			intVasr.addTransformer(new Pair<>(resetVectorInt, additionVectorInt));
		}
		return new IntvasrAbstraction(integerSimulationMatrix, intVasr);
	}

	public static IntVasrsAbstraction qvasrsAbstactionToIntVasrsAbstraction(final ManagedScript script,
			final QvasrsAbstraction qvasrsAbstraction) {
		final BigInteger lcm = getLeastCommonMultiple(qvasrsAbstraction.getAbstraction());
		final IntvasrAbstraction intVasrAbstraction = qvasrAbstractionToInt(qvasrsAbstraction.getAbstraction());
		final Map<IProgramVar, TermVariable> intInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> intOutVars = new HashMap<>();

		final Map<Term, Term> inVarSub = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> inVar : qvasrsAbstraction.getInVars().entrySet()) {
			final TermVariable intVar =
					script.constructFreshTermVariable(inVar.getValue().getName(), SmtSortUtils.getIntSort(script));
			intInVars.put(inVar.getKey(), intVar);
			inVarSub.put(inVar.getValue(), intVar);
		}

		for (final Entry<IProgramVar, TermVariable> outVar : qvasrsAbstraction.getOutVars().entrySet()) {
			final TermVariable intVar =
					script.constructFreshTermVariable(outVar.getValue().getName(), SmtSortUtils.getIntSort(script));
			intOutVars.put(outVar.getKey(), intVar);
			inVarSub.put(outVar.getValue(), intVar);
		}

		final IntVasrsAbstraction intVasrsAbstraction =
				new IntVasrsAbstraction(intVasrAbstraction, qvasrsAbstraction.getStates(), intInVars, intOutVars,
						qvasrsAbstraction.getPreState(), qvasrsAbstraction.getPostState());
		final Set<Term> intStates = new HashSet<>();
		for (final Triple<Term, Pair<Rational[], Rational[]>, Term> transition : qvasrsAbstraction.getTransitions()) {
			final Term intSource = Substitution.apply(script, inVarSub, transition.getFirst());
			final Term intTarget = Substitution.apply(script, inVarSub, transition.getThird());
			intStates.add(intTarget);
			intStates.add(intSource);
			final Integer[] resetVectorInt = new Integer[transition.getSecond().getFirst().length];
			final Integer[] additionVectorInt = new Integer[transition.getSecond().getFirst().length];
			for (int i = 0; i < transition.getSecond().getFirst().length; i++) {
				resetVectorInt[i] = transition.getSecond().getFirst()[i].numerator().intValue();
				final Rational oldRationalEntry = transition.getSecond().getSecond()[i].mul(lcm);
				assert oldRationalEntry.isIntegral();
				additionVectorInt[i] = oldRationalEntry.numerator().intValue();
			}
			final Triple<Term, Pair<Integer[], Integer[]>, Term> intTranstion =
					new Triple<>(intSource, new Pair<>(resetVectorInt, additionVectorInt), intTarget);
			intVasrsAbstraction.addTransition(intTranstion);
		}
		intVasrsAbstraction.setStates(intStates);
		final Term newPre = Substitution.apply(script, inVarSub, qvasrsAbstraction.getPreState());
		final Term newPost = Substitution.apply(script, inVarSub, qvasrsAbstraction.getPostState());
		intVasrsAbstraction.setPreState(newPre);
		intVasrsAbstraction.setPostState(newPost);
		return intVasrsAbstraction;
	}
}
