/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult.JordanTransformationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate.SimultaneousUpdateException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanLoopAcceleration {

	private static final boolean CONCATENATE_WITH_NEGATION_OF_GUARD = false;

	private JordanLoopAcceleration() {
		// do not instantiate
	}

	/**
	 * Loop acceleration for loops with linear updates, where only -1,0,1 are eigenvalues of the update matrix. Remark:
	 * the main parts of this algorithm also work if eigenvalues are (complex) roots of unity with a suitable
	 * representation of complex numbers.
	 */
	public static JordanLoopAccelerationResult accelerateLoop(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final UnmodifiableTransFormula loopTransFormula,
			final boolean quantifyItFinExplicitly) {
		final ILogger logger = services.getLoggingService().getLogger(JordanLoopAcceleration.class);
		final SimultaneousUpdate su;
		try {
			su = SimultaneousUpdate.fromTransFormula(loopTransFormula, mgdScript);
		} catch (final SimultaneousUpdateException e) {
			final JordanLoopAccelerationStatisticsGenerator jlasg =
					new JordanLoopAccelerationStatisticsGenerator(-1, -1, -1, new NestedMap2<>());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.SIMULTANEOUS_UPDATE_FAILED, e.getMessage(), null,
					jlasg);
		}
		final int numberOfAssignedVariables = su.getDeterministicAssignment().size();
		final int numberOfHavocedVariables = su.getHavocedVars().size();

		final Set<Sort> nonIntegerSorts = getNonIntegerSorts(su.getDeterministicAssignment().keySet());
		if (!nonIntegerSorts.isEmpty()) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, -1, new NestedMap2<>());
			final String errorMessage = "Some updated variables are of non-integer sorts : " + nonIntegerSorts;
			return new JordanLoopAccelerationResult(JordanLoopAccelerationResult.AccelerationStatus.NONINTEGER_UPDATE,
					errorMessage, null, jlasg);
		}

		final Pair<LinearUpdate, String> pair = extractLinearUpdate(mgdScript, su);
		if (pair.getFirst() == null) {
			assert pair.getSecond() != null;
			final JordanLoopAccelerationStatisticsGenerator jlasg =
					new JordanLoopAccelerationStatisticsGenerator(numberOfAssignedVariables,
							numberOfHavocedVariables, -1, new NestedMap2<>());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.NONLINEAR_UPDATE, pair.getSecond(), null, jlasg);
		}
		final int numberOfReadonlyVariables = pair.getFirst().getReadonlyVariables().size();

		// HashMap to get matrix index from TermVariable.
		final HashMap<Term, Integer> varMatrixIndexMap = determineMatrixIndices(pair.getFirst());
		final QuadraticMatrix updateMatrix = computeUpdateMatrix(mgdScript, pair.getFirst(), varMatrixIndexMap);

		final JordanTransformationResult jordanUpdate = updateMatrix.constructJordanTransformation();

		if (jordanUpdate.getStatus() == JordanTransformationStatus.UNSUPPORTED_EIGENVALUES) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, numberOfReadonlyVariables, new NestedMap2<>());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.UNSUPPORTED_EIGENVALUES, null, null, jlasg);
		}
		assert isBlockSizeConsistent(numberOfAssignedVariables, numberOfReadonlyVariables,
				jordanUpdate) : "inconsistent blocksize";

		final boolean isAlternatingClosedFormRequired = isAlternatingClosedFormRequired(jordanUpdate);
		final UnmodifiableTransFormula guardTf =
				TransFormulaUtils.computeGuard(loopTransFormula, mgdScript, services);
		final UnmodifiableTransFormula loopAccelerationFormula =
				createLoopAccelerationFormula(logger, services, mgdScript, su, varMatrixIndexMap, jordanUpdate,
						loopTransFormula, guardTf, true, quantifyItFinExplicitly, isAlternatingClosedFormRequired);
		final JordanLoopAccelerationStatisticsGenerator jlasg =
				new JordanLoopAccelerationStatisticsGenerator(numberOfAssignedVariables, numberOfHavocedVariables,
						numberOfReadonlyVariables, jordanUpdate.getJordanBlockSizes());
		if (isAlternatingClosedFormRequired) {
			jlasg.reportAlternatingAcceleration();
		} else {
			jlasg.reportSequentialAcceleration();
		}

		if (QuantifierUtils.isQuantifierFree(loopAccelerationFormula.getFormula())) {
			jlasg.reportQuantifierFreeResult();
		}

		return new JordanLoopAccelerationResult(JordanLoopAccelerationResult.AccelerationStatus.SUCCESS, null,
				loopAccelerationFormula, jlasg);
	}

	private static Pair<LinearUpdate, String> extractLinearUpdate(final ManagedScript mgdScript,
			final SimultaneousUpdate su) {
		final Set<TermVariable> termVariablesOfModified = new HashSet<>();
		for (final Entry<IProgramVar, Term> update : su.getDeterministicAssignment().entrySet()) {
			termVariablesOfModified.add(update.getKey().getTermVariable());
		}
		for (final IProgramVar pv : su.getHavocedVars()) {
			termVariablesOfModified.add(pv.getTermVariable());
		}
		final Set<Term> readonlyVariables = new HashSet<>();
		final Map<TermVariable, AffineTerm> updateMap = new HashMap<>();
		for (final Entry<IProgramVar, Term> update : su.getDeterministicAssignment().entrySet()) {
			final Triple<AffineTerm, Set<Term>, String> triple = extractLinearUpdate(mgdScript, termVariablesOfModified,
					update);
			if (triple.getFirst() == null) {
				assert triple.getSecond() == null;
				assert triple.getThird() != null;
				return new Pair<>(null, triple.getThird());
			} else {
				assert triple.getSecond() != null;
				assert triple.getThird() == null;
				updateMap.put(update.getKey().getTermVariable(), triple.getFirst());
				readonlyVariables.addAll(triple.getSecond());
			}
		}
		return new Pair<>(new LinearUpdate(updateMap, readonlyVariables), null);
	}

	private static Triple<AffineTerm, Set<Term>, String> extractLinearUpdate(final ManagedScript mgdScript,
			final Set<TermVariable> termVariablesOfModified, final Entry<IProgramVar, Term> update) {
		final IPolynomialTerm polyRhs = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
				.transform(update.getValue());
		final Map<Term, Rational> variables2coeffcient = new HashMap<>();
		final Set<Term> readonlyVariables = new HashSet<>();
		for (final Entry<Monomial, Rational> entry : polyRhs.getMonomial2Coefficient().entrySet()) {
			final Term monomialAsTerm = entry.getKey().toTerm(mgdScript.getScript());
			if (!termVariablesOfModified.contains(monomialAsTerm)) {
				final TermVariable termVariableOfModified = containsTermVariableOfModified(termVariablesOfModified,
						monomialAsTerm);
				if (termVariableOfModified != null) {
					final String errorMessage = String.format(
							"Monomial contains modified variable. Monomial %s, Variable %s", monomialAsTerm,
							termVariableOfModified);
					return new Triple<AffineTerm, Set<Term>, String>(null, null, errorMessage);
				} else {
					readonlyVariables.add(monomialAsTerm);
				}
			}
			variables2coeffcient.put(monomialAsTerm, entry.getValue());
		}
		final AffineTerm affineTerm = new AffineTerm(polyRhs.getSort(), polyRhs.getConstant(), variables2coeffcient);
		return new Triple<AffineTerm, Set<Term>, String>(affineTerm, readonlyVariables, null);
	}

	private static TermVariable containsTermVariableOfModified(final Set<TermVariable> termVariablesOfModified,
			final Term monomialAsTerm) {
		for (final TermVariable tv : monomialAsTerm.getFreeVars()) {
			if (termVariablesOfModified.contains(tv)) {
				return tv;
			}
		}
		return null;
	}

	/**
	 * The sum of the sizes of all block is the sum of the number of assigned variables, the number of unmodified
	 * variables and one (one is for the numbers that are added in the loop).
	 */
	private static boolean isBlockSizeConsistent(final int numberOfAssignedVariables,
			final int numberOfUnmodifiedVariables, final JordanTransformationResult jordanUpdate) {
		int blockSizeSum = 0;
		for (final Triple<Integer, Integer, Integer> triple : jordanUpdate.getJordanBlockSizes().entrySet()) {
			blockSizeSum += triple.getSecond() * triple.getThird();
		}
		return (numberOfAssignedVariables + numberOfUnmodifiedVariables + 1 == blockSizeSum);
	}

	private static Set<Sort> getNonIntegerSorts(final Set<IProgramVar> programVariables) {
		final Set<Sort> result = new HashSet<>();
		for (final IProgramVar pv : programVariables) {
			if (!SmtSortUtils.isIntSort(pv.getSort())) {
				result.add(pv.getSort());
			}
		}
		return result;
	}

	/**
	 * @return true iff -1 is an eigenvalue or for eigenvalue 1 there is a Jordan block of size greater than 2.
	 */
	private static boolean isAlternatingClosedFormRequired(final JordanTransformationResult jordanUpdate) {
		final boolean minus1isEigenvalue = jordanUpdate.getJordanBlockSizes().containsKey(-1);
		final boolean ev1hasBlockGreater2 = hasEv1JordanBlockStrictlyGreater2(jordanUpdate);
		return (minus1isEigenvalue || ev1hasBlockGreater2);
	}

	/**
	 * Go through terms, get all variables and create a hash map varMatrixIndex with variables as key and corresponding
	 * matrix index as value to save which column corresponds to which variable and which row corresponds to which
	 * update.
	 */
	private static HashMap<Term, Integer> determineMatrixIndices(final LinearUpdate linearUpdate) {
		final HashMap<Term, Integer> varMatrixIndex = new HashMap<>();
		int i = 0;
		// add all updated variables.
		for (final TermVariable updatedVar : linearUpdate.getUpdateMap().keySet()) {
			assert !varMatrixIndex.containsKey(updatedVar) : "cannot add same variable twice";
			varMatrixIndex.put(updatedVar, i);
			i++;
		}
		// add all variables that are only read in updates
		for (final Term var : linearUpdate.getReadonlyVariables()) {
			assert !varMatrixIndex.containsKey(var) : "cannot add same variable twice";
			varMatrixIndex.put(var, i);
			i++;
		}
		return varMatrixIndex;
	}

	/**
	 * Fills the row corresponding to variable of the updateMatrix where variable is updated with polyRhs.
	 */
	private static void fillMatrixRow(final QuadraticMatrix updateMatrix,
			final HashMap<Term, Integer> varMatrixIndexMap, final AffineTerm affineRhs, final TermVariable tv) {

		final int n = updateMatrix.getDimension() - 1;
		updateMatrix.setEntry(n, n, BigInteger.valueOf(1));
		// Set diagonal entry to 0 for case variable assignment does not depend on
		// variable itself
		// (matrix was initialized as identity matrix).
		updateMatrix.setEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(tv), BigInteger.valueOf(0));

		// Fill row.
		for (final Term termVar : varMatrixIndexMap.keySet()) {
			updateMatrix.setEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(termVar),
					determineCoefficient(affineRhs, termVar));
			if (updateMatrix.getEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(termVar)) == null) {
				// not a linear term.
				break;
			}
			updateMatrix.setEntry(varMatrixIndexMap.get(tv), n, determineConstant(affineRhs));
		}
	}

	/**
	 * Determine the coefficient of termVar in the {@link AffineTerm} affineRhs.
	 */
	private static BigInteger determineCoefficient(final AffineTerm affineRhs, final Term termVar) {
		final Rational coefficient = affineRhs.getVariable2Coefficient().get(termVar);
		if (coefficient != null) {
			if (!coefficient.isIntegral()) {
				throw new AssertionError("Some coefficient is not integral.");
			}
			return coefficient.numerator();

		} else {
			return BigInteger.ZERO;
		}
	}

	/**
	 * Determine the constant term in the polynomial polyRhs.
	 */
	private static BigInteger determineConstant(final IPolynomialTerm polyRhs) {
		final Rational constant = polyRhs.getConstant();
		if (!constant.denominator().equals(BigInteger.valueOf(1))) {
			throw new AssertionError("Constant in some term is not integral.");
		}
		return constant.numerator();
	}

	/**
	 * Computes the closed form, a hashmap mapping a variable to the corresponding closed form term, out of the closed
	 * form matrix.
	 */
	private static HashMap<IProgramVar, Term> matrix2ClosedFormOfUpdate(final ManagedScript mgdScript,
			final PolynomialTermMatrix closedFormMatrix, final HashMap<Term, Integer> var2MatrixIndex,
			final SimultaneousUpdate su, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		final HashMap<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
			substitutionMapping.put(entry.getKey().getTermVariable(), entry.getValue());
		}
		// Array to get TermVariable from matrix index.
		final Term[] matrixIndex2Var = new Term[var2MatrixIndex.size()];
		for (final Term var : var2MatrixIndex.keySet()) {
			matrixIndex2Var[var2MatrixIndex.get(var)] = var;
		}
		final HashMap<IProgramVar, Term> closedForm = new HashMap<>();
		for (final IProgramVar pv : su.getDeterministicAssignment().keySet()) {
			final TermVariable tv = pv.getTermVariable();
			Term sum = constructClosedForm(mgdScript, closedFormMatrix, var2MatrixIndex, matrixIndex2Var, tv);
			sum = Substitution.apply(mgdScript, substitutionMapping, sum);
			closedForm.put(pv, sum);
		}
		return closedForm;
	}

	private static Term constructClosedForm(final ManagedScript mgdScript, final PolynomialTermMatrix closedFormMatrix,
			final HashMap<Term, Integer> var2MatrixIndex, final Term[] matrixIndex2Var, final TermVariable tv) {
		final int varIndex = var2MatrixIndex.get(tv);
		final int n = closedFormMatrix.getDimension();
		final Term[] summands = new Term[n];
		int current = 0;
		for (int j = 0; j < n - 1; j++) {
			// Ignore if matrix entry is 0.
			if (closedFormMatrix.getEntry(varIndex, j).isConstant()) {
				final Rational entryRational = closedFormMatrix.getEntry(varIndex, j).getConstant();
				if (entryRational.numerator().intValue() == 0) {
					continue;
				}
			}
			// If matrix entry is 1, only add variable.
			if (closedFormMatrix.getEntry(varIndex, j).isConstant()) {
				final Rational entryRational = closedFormMatrix.getEntry(varIndex, j).getConstant();
				if (entryRational.numerator().intValue() == 1 && entryRational.denominator().intValue() == 1) {
					summands[current] = matrixIndex2Var[j];
				} else {
					summands[current] = mgdScript.getScript().term("*", closedFormMatrix.getEntry(varIndex, j).toTerm(mgdScript.getScript()),
							matrixIndex2Var[j]);
				}
			} else {
				summands[current] = mgdScript.getScript().term("*", closedFormMatrix.getEntry(varIndex, j).toTerm(mgdScript.getScript()),
						matrixIndex2Var[j]);
			}
			current = current + 1;
		}
		// Add constant term if it is not zero.
		if (closedFormMatrix.getEntry(varIndex, n - 1).isConstant()) {
			final Rational entryRational = closedFormMatrix.getEntry(varIndex, n - 1).getConstant();
			if (entryRational.numerator().intValue() != 0) {
				summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(mgdScript.getScript());
				current = current + 1;
			}
		} else {
			summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(mgdScript.getScript());
			current = current + 1;
		}
		Term sum = mgdScript.getScript().numeral(BigInteger.ZERO);
		if (current == 0) {
			sum = mgdScript.getScript().numeral(BigInteger.ZERO);
		} else if (current == 1) {
			sum = summands[0];
		} else {
			sum = mgdScript.getScript().term("+", Arrays.copyOfRange(summands, 0, current));
		}
		return sum;
	}

	/**
	 * Compute the update matrix out of the simultaneous update.
	 */
	private static QuadraticMatrix computeUpdateMatrix(final ManagedScript mgdScript, final LinearUpdate linearUpdate,
			final HashMap<Term, Integer> varMatrixIndexMap) {

		final int n = varMatrixIndexMap.size() + 1;

		// Initialize update matrix with identity matrix (every variable assigned to itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.constructIdentityMatrix(n);

		// Fill update matrix.
		for (final Entry<TermVariable, AffineTerm> update : linearUpdate.getUpdateMap().entrySet()) {
			fillMatrixRow(updateMatrix, varMatrixIndexMap, update.getValue(), update.getKey());
			for (int j = 0; j < n; j++) {
				if (updateMatrix.getEntry(varMatrixIndexMap.get(update.getKey()), j) == null) {
					return null;
				}
			}
		}
		return updateMatrix;
	}

	/**
	 * Compute the closed form given the update, the update matrix and the corresponding jordan matrix.
	 */
	private static Pair<HashMap<IProgramVar, Term>, Boolean> computeClosedFormOfUpdate(final ManagedScript mgdScript,
			final SimultaneousUpdate su, final HashMap<Term, Integer> varMatrixIndexMap,
			final JordanTransformationResult jordanUpdate, final TermVariable it, final TermVariable itHalf,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final boolean itEven, final boolean restrictedVersionPossible) {

		final RationalMatrix modalUpdate = jordanUpdate.getModal();
		final RationalMatrix inverseModalUpdate = jordanUpdate.getInverseModal();

		// Compute matrix that represents closed form.
		final Pair<PolynomialTermMatrix, Boolean> closedFormMatrix =
				PolynomialTermMatrix.computeClosedFormMatrix(mgdScript, modalUpdate, jordanUpdate, inverseModalUpdate,
						it, itHalf, itEven, restrictedVersionPossible);
		if (!closedFormMatrix.getValue()) {
			final Pair<HashMap<IProgramVar, Term>, Boolean> result = new Pair<>(null, false);
			return result;
		}
		final HashMap<IProgramVar, Term> closedForm = matrix2ClosedFormOfUpdate(mgdScript,
				closedFormMatrix.getKey(), varMatrixIndexMap, su, inVars, outVars);
		final Pair<HashMap<IProgramVar, Term>, Boolean> result = new Pair<>(closedForm, true);
		return result;
	}

	/**
	 * Computes the term guard(closedForm(inVars)).
	 *
	 * @param havocVarReplacements Map that assigns variables that are havoced the term
	 *                         with which they should be replaced.
	 */
	private static Term constructGuardOfClosedForm(final ManagedScript mgdScript,
			final UnmodifiableTransFormula guardTf, final HashMap<IProgramVar, Term> closedFormOfUpdate,
			final HashMap<IProgramVar, TermVariable> havocVarReplacements) {
		final Map<IProgramVar, Term> map = new HashMap<>();
		for (final IProgramVar pv : guardTf.getInVars().keySet()) {
			final Term updateTerm = closedFormOfUpdate.get(pv);
			if (updateTerm != null) {
				map.put(pv, updateTerm);
			} else {
				final TermVariable auxVar = havocVarReplacements.get(pv);
				if (auxVar != null) {
					map.put(pv, auxVar);
				} else {
					map.put(pv, guardTf.getInVars().get(pv));
				}
			}
		}
		return TransFormulaUtils.renameInvars(guardTf, mgdScript, map);
	}

	/**
	 * Create the loop Acceleration formula.
	 *
	 * @param isAlternatingClosedFormRequired
	 *            If set we construct a closed from that consists of two formulas one for even iteration steps and one
	 *            for odd iteration steps. Otherwise the is one closed form for all iteration steps.
	 */
	private static UnmodifiableTransFormula createLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final HashMap<Term, Integer> varMatrixIndexMap, final JordanTransformationResult jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final boolean restrictedVersionPossible, final boolean quantifyItFinExplicitly,
			final boolean isAlternatingClosedFormRequired) {

		final UnmodifiableTransFormula loopAccelerationFormula;
		final Map<IProgramVar, TermVariable> inVars =
				new HashMap<IProgramVar, TermVariable>(loopTransFormula.getInVars());
		final Term xPrimeEqualsX = constructXPrimeEqualsX(mgdScript, inVars, loopTransFormula.getOutVars());
		if (isAlternatingClosedFormRequired) {
			final TermVariable itFinHalf =
					mgdScript.constructFreshTermVariable("itFinHalf", SmtSortUtils.getIntSort(mgdScript.getScript()));
			final Term loopAccelerationTerm = createLoopAccelerationTermAlternating(logger, services, mgdScript, su,
					varMatrixIndexMap, jordanUpdate, loopTransFormula, guardTf, quantifyItFinExplicitly, itFinHalf,
					xPrimeEqualsX, inVars);
			loopAccelerationFormula = buildAccelerationFormula(logger, mgdScript, services, loopTransFormula,
					loopAccelerationTerm, quantifyItFinExplicitly, itFinHalf, inVars);
		} else {
			final TermVariable itFin =
					mgdScript.constructFreshTermVariable("itFin", SmtSortUtils.getIntSort(mgdScript.getScript()));
			final Term loopAccelerationTerm = createLoopAccelerationTermSequential(logger, services, mgdScript, su,
					varMatrixIndexMap, jordanUpdate, loopTransFormula, guardTf, restrictedVersionPossible,
					quantifyItFinExplicitly, itFin, xPrimeEqualsX, inVars);
			loopAccelerationFormula = buildAccelerationFormula(logger, mgdScript, services, loopTransFormula,
					loopAccelerationTerm, quantifyItFinExplicitly, itFin, inVars);
		}
		return loopAccelerationFormula;
	}

	/**
	 * @return true iff there is some Jordan block for eigenvalue 1 whose size is strictly greater than 2
	 */
	private static boolean hasEv1JordanBlockStrictlyGreater2(final JordanTransformationResult jordanUpdate) {
		boolean ev1hasBlockGreater2 = false;
		for (final int blockSize : jordanUpdate.getJordanBlockSizes().get(1).keySet()) {
			if (blockSize > 2 && (jordanUpdate.getJordanBlockSizes().get(1).get(blockSize) != 0)) {
				ev1hasBlockGreater2 = true;
			}
		}
		return ev1hasBlockGreater2;
	}

	/**
	 * Simplify the term representing the loop acceleration formula and build UnmodifiableTransFormula.
	 */
	private static UnmodifiableTransFormula buildAccelerationFormula(final ILogger logger,
			final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final UnmodifiableTransFormula loopTransFormula, final Term loopAccelerationTerm,
			final boolean quantifyItFinExplicitly, final TermVariable itFin,
			final Map<IProgramVar, TermVariable> inVars) {
		UnmodifiableTransFormula loopAccelerationFormula;

		final Term nnf =
				new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = PartialQuantifierElimination.eliminateCompat(services,
				mgdScript, true, PqeTechniques.ALL, SimplificationTechnique.NONE, nnf);
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

		if (quantifyItFinExplicitly) {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, loopTransFormula.getOutVars(),
					loopTransFormula.getNonTheoryConsts().isEmpty(), loopTransFormula.getNonTheoryConsts(),
					loopTransFormula.getBranchEncoders().isEmpty(), loopTransFormula.getBranchEncoders(),
					loopTransFormula.getAuxVars().isEmpty());
			tfb.setInfeasibility(loopTransFormula.isInfeasible());
			tfb.setFormula(simplified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);
			// Correctness of quantifier elimination is checked within
			// checkPropertiesOfLoopAccelerationFormula.
		} else {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, loopTransFormula.getOutVars(),
					loopTransFormula.getNonTheoryConsts().isEmpty(), loopTransFormula.getNonTheoryConsts(),
					loopTransFormula.getBranchEncoders().isEmpty(), loopTransFormula.getBranchEncoders(), false);

			tfb.addAuxVar(itFin);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
			tfb.setFormula(simplified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);

			// Check correctness of quantifier elimination.
			assert checkCorrectnessOfQuantifierElimination(logger, mgdScript.getScript(), loopAccelerationTerm,
					simplified);
		}
		return loopAccelerationFormula;
	}

	/**
	 * Create the loop acceleration formula. If -1 is an eigenvalue or there is a Jordan block greater 2 for eigenvalue
	 * 1 return null. General formula:
	 *
	 * <pre>
	 * (exists ((itFin Int))
	 * ((or
	 * 	(and (= itFin 0) (not (guard(x)) (x'=x))
	 * 	(and
	 * 		(> itFin 0)
	 * 		(not (guard(closedForm(x, itFin))))
	 * 		(guard(x))
	 * 		(forall ((it Int))
	 * 			(=>
	 * 				(and (<= 1 it) (<= it (- itFin 1)))
	 * 				(guard(closedForm(x,it)))))
	 * 		((x' = closedForm(x,itFin)))))))
	 * </pre>
	 *
	 * @param services
	 * @param mgdScript
	 * @param su
	 * @param loopTransFormula
	 * @param guardTf
	 * @return
	 */
	private static Term createLoopAccelerationTermSequential(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final HashMap<Term, Integer> varMatrixIndexMap, final JordanTransformationResult jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final boolean restrictedVersionPossible, final boolean quantifyItFinExplicitly, final TermVariable itFin,
			final Term xPrimeEqualsX, final Map<IProgramVar, TermVariable> inVars) {
		final Script script = mgdScript.getScript();

		final Pair<HashMap<IProgramVar, Term>, Boolean> closedFormItFinTuple =
				computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap, jordanUpdate, itFin, null,
						loopTransFormula.getInVars(), loopTransFormula.getOutVars(), true, restrictedVersionPossible);
		if (!closedFormItFinTuple.getValue()) {
			return null;
		}
		final HashMap<IProgramVar, Term> closedFormItFin = closedFormItFinTuple.getKey();

		final List<Term> conjuncts = new ArrayList<Term>();

		if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
			// Construct subformula guard(cf(x,itFin)).
			final Term guardOfClosedFormItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
					loopTransFormula.getOutVars(), guardTf, closedFormItFin);
			// (not (guard(closedForm(x, itFin))))
			final Term notGuardOfCf = Util.not(script, guardOfClosedFormItFin);
			conjuncts.add(notGuardOfCf);
		}

		// (> itFin 0)
		final Term firstConjunct = script.term(">", itFin, script.numeral(BigInteger.ZERO));
		conjuncts.add(firstConjunct);

		// (forall ((it Int)) (=> (and (<= 1 it) (<= it (- itFin 1)))
		// (guard(closedForm(x,it)))))
		final TermVariable it = mgdScript.constructFreshTermVariable("it", SmtSortUtils.getIntSort(script));
		final Term fourthConjunct;
		final Term guardOfClosedFormIt;
		{
			final Term itGreater1 = script.term("<=", script.numeral(BigInteger.ONE), it);
			final Term itSmallerItFinM1 = script.term("<=", it,
					script.term("-", itFin, script.numeral(BigInteger.ONE)));
			final HashMap<IProgramVar, Term> closedFormIt = computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap,
					jordanUpdate, it, null, inVars, loopTransFormula.getOutVars(), true, restrictedVersionPossible)
							.getKey();
			guardOfClosedFormIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
					guardTf, closedFormIt);
			final Term leftSideOfImpl = Util.and(script, itGreater1, itSmallerItFinM1);
			final Term implication = Util.implies(script, leftSideOfImpl, guardOfClosedFormIt);
			final Set<TermVariable> itSet = new HashSet<>();
			itSet.add(it);
			fourthConjunct = SmtUtils.quantifier(script, 1, itSet, implication);
		}
		conjuncts.add(fourthConjunct);

		// (x' = closedForm(x,itFin))
		final Term xPrimed = constructClosedUpdateConstraint(script, loopTransFormula, su.getHavocedVars(), closedFormItFin);
		conjuncts.add(xPrimed);

		conjuncts.add(guardTf.getFormula());
		final Term conjunction = SmtUtils.and(script, conjuncts);

		// (and (= itFin 0) (not (guard)) (x'=x))
		final Term zeroIterationCase;
		{
			final Term itFinIs0 = script.term("=", itFin, script.numeral(BigInteger.ZERO));
			final Term notGuard = Util.not(script, guardTf.getFormula());
			zeroIterationCase = Util.and(script, itFinIs0, notGuard, xPrimeEqualsX);
		}
		final Term disjunction = Util.or(script, zeroIterationCase, conjunction);

		final Set<TermVariable> itFinSet = new HashSet<>();
		itFinSet.add(itFin);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinSet, disjunction);

		assert checkPropertiesOfLoopAccelerationFormula(logger, services, mgdScript, loopTransFormula, inVars,
				loopAccelerationTerm, guardTf, xPrimeEqualsX, guardOfClosedFormIt, guardOfClosedFormIt, it, true);

		if (quantifyItFinExplicitly) {
			return loopAccelerationTerm;
		} else {
			return disjunction;
		}
	}

	private static Term constructGuardAfterIntermediateIterations(final ManagedScript mgdScript,
			final Set<IProgramVar> havocedVars, final UnmodifiableTransFormula guardTf,
			final HashMap<IProgramVar, Term> closedFormIt) {
		final HashMap<IProgramVar, TermVariable> havocReplacements = constructHavocReplacementsForIntermediateIteration(
				mgdScript, havocedVars);
		final Set<TermVariable> havocVarSet = new HashSet<>(havocReplacements.values());
		final Term guardOfClosedFormItUnquantified = constructGuardOfClosedForm(mgdScript, guardTf, closedFormIt,
				havocReplacements);
		return SmtUtils.quantifier(mgdScript.getScript(), QuantifiedFormula.EXISTS, havocVarSet,
				guardOfClosedFormItUnquantified);
	}

	private static Term constructGuardAfterFinalIteration(final ManagedScript mgdScript,
			final Set<IProgramVar> havocedVars, final Map<IProgramVar, TermVariable> outVars,
			final UnmodifiableTransFormula guardTf, final HashMap<IProgramVar, Term> closedFormItFin) {
		final HashMap<IProgramVar, TermVariable> havocReplacements = constructHavocReplacementsForFinalIteration(
				havocedVars, outVars);
		return constructGuardOfClosedForm(mgdScript, guardTf, closedFormItFin, havocReplacements);
	}

	private static HashMap<IProgramVar, TermVariable> constructHavocReplacementsForIntermediateIteration(
			final ManagedScript mgdScript, final Set<IProgramVar> havocedVars) {
		final HashMap<IProgramVar, TermVariable> havocReplacements = new HashMap<>();
		for (final IProgramVar pv : havocedVars) {
			final String varName = pv.getTermVariable().getName() + "_havocIntermIteration";
			havocReplacements.put(pv, mgdScript.variable(varName, pv.getSort()));
		}
		return havocReplacements;
	}

	private static HashMap<IProgramVar, TermVariable> constructHavocReplacementsForFinalIteration(
			final Set<IProgramVar> havocedVars, final Map<IProgramVar, TermVariable> outVars) {
		final HashMap<IProgramVar, TermVariable> havocReplacements = new HashMap<>();
		for (final IProgramVar pv : havocedVars) {
			havocReplacements.put(pv, outVars.get(pv));
		}
		return havocReplacements;
	}


	private static Term constructClosedUpdateConstraint(final Script script, final UnmodifiableTransFormula loopTf,
			final Set<IProgramVar> havocedVars, final Map<IProgramVar, Term> closedForm) {
		final List<Term> equalities = new ArrayList<>();
		for (final IProgramVar var : loopTf.getOutVars().keySet()) {
			if (!havocedVars.contains(var)) {
				final Term lhs = loopTf.getOutVars().get(var);
				final Term rhs;
				if (closedForm.containsKey(var)) {
					rhs = closedForm.get(var);
				} else {
					rhs = loopTf.getInVars().get(var);
				}
				final Term equality = SmtUtils.binaryEquality(script, lhs, rhs);
				equalities.add(equality);
			}
		}
		return SmtUtils.and(script, equalities);

	}

	/**
	 * Create the loop acceleration formula. Used if restricted version fails. General formula:
	 *
	 * <pre>
	 * (exists ((itFinHalf Int))
	 * (or
	 * 	// itFin even
	 * 	(or
	 * 		(and (= itFinHalf 0) (not (guard(x))) (x'=x))
	 * 		(and
	 * 			(> itFinHalf 0)
	 * 			(guard(x))
	 * 			(not (guard(closedFormEven(x, 2*itFinHalf))))
	 * 			(forall ((itHalf Int))
	 * 				(and
	 * 					(=>
	 * 						(and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
	 * 						(guard(closedFormEven(x, 2*itHalf))))
	 * 					(=>
	 * 						(and (<= 0 itHalf) (<= itHalf (- itFinHalf 1)))
	 * 						(guard(closedFormOdd(x, 2*itHalf+1))))))
	 * 			(x' = closedFormEven(x,2*itFinHalf))))
	 *
	 * 	// itFin odd
	 * 	(and
	 * 		(>= itFinHalf 0)
	 * 		(guard(x))
	 * 		(not (guard(closedFormOdd(x, 2*itFinHalf+1))))
	 * 		(forall ((itHalf Int))
	 * 			(and
	 * 				(=>
	 * 					(and (<= 1 itHalf) (<= itHalf itFinHalf))
	 * 					(guard(closedFormEven(x, 2*itHalf))))
	 * 				(=>
	 * 					(and (<= 0 itHalf) (<= itHalf (- itFinHalf 1)))
	 * 					(guard(closedFormOdd(x, 2*itHalf+1))))))
	 * 		(x' = closedFormOdd(x,2*itFinHalf+1)))))
	 * </pre>
	 *
	 * @param services
	 * @param mgdScript
	 * @param su
	 * @param loopTransFormula
	 * @param guardTf
	 * @return
	 */
	private static Term createLoopAccelerationTermAlternating(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final HashMap<Term, Integer> varMatrixIndexMap, final JordanTransformationResult jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final boolean quantifyItFinExplicitly, final TermVariable itFinHalf, final Term xPrimeEqualsX,
			final Map<IProgramVar, TermVariable> inVars) {

		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);

		// (and (= itFinHalf 0) (not (guard)) (x'=x))
		// final TermVariable itFinHalf = mgdScript.constructFreshTermVariable("itFinHalf", sort);
		final Term itFinHalfEquals0 = script.term("=", itFinHalf, script.numeral(BigInteger.ZERO));
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term firstFinalDisjunctEven = Util.and(script, itFinHalfEquals0, notGuard, xPrimeEqualsX);

		// (> itFinHalf 0)
		final Term itFinHalfGreater0 = script.term(">", itFinHalf, script.numeral(BigInteger.ZERO));

		// (not (guard(closedFormEven(x, 2*itFinHalf))))
		final HashMap<IProgramVar, Term> closedFormEvenItFin =
				computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap, jordanUpdate, null, itFinHalf, inVars,
						loopTransFormula.getOutVars(), true, false).getKey();
		final Term guardOfClosedFormEvenItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormEvenItFin);

		final HashMap<IProgramVar, Term> closedFormOddItFin =
				computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap, jordanUpdate, null, itFinHalf, inVars,
						loopTransFormula.getOutVars(), false, false).getKey();
		final Term guardOfClosedFormOddItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormOddItFin);

		// ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
		final TermVariable itHalf = mgdScript.constructFreshTermVariable("itHalf", sort);
		final Term oneLeqItHalf = script.term("<=", script.numeral(BigInteger.ONE), itHalf);
		final Term itHalfLeqItFinHalfM1 =
				script.term("<=", itHalf, script.term("-", itFinHalf, script.numeral(BigInteger.ONE)));
		final Term forallTerm1Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormEven(x, 2*itHalf)))
		final HashMap<IProgramVar, Term> closedFormEvenIt = computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap,
				jordanUpdate, null, itHalf, inVars, loopTransFormula.getOutVars(), true, false).getKey();
		final Term guardOfClosedFormEvenIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
				guardTf, closedFormEvenIt);

		// (=> ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term forallTerm1Implication1 = Util.implies(script, forallTerm1Implication1Left, guardOfClosedFormEvenIt);

		// ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1))))
		final Term zeroLeqItHalf = script.term("<=", script.numeral(BigInteger.ZERO), itHalf);
		final Term forallTerm1Implication2Left = Util.and(script, zeroLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormOdd(x, 2*itHalf+1))
		final HashMap<IProgramVar, Term> closedFormOddIt = computeClosedFormOfUpdate(mgdScript, su, varMatrixIndexMap,
				jordanUpdate, null, itHalf, inVars, loopTransFormula.getOutVars(), false, false).getKey();
		final Term guardOfClosedFormOddIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
				guardTf, closedFormOddIt);

		// (=> ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1)))) (guard(closedFormOdd(x,
		// 2*itHalf+1)))))))
		final Term forallTerm1Implication2 = Util.implies(script, forallTerm1Implication2Left, guardOfClosedFormOddIt);

		// (and implication1 implication2)
		final Term forallTermConjunction1 = Util.and(script, forallTerm1Implication1, forallTerm1Implication2);

		final Set<TermVariable> itHalfSet = new HashSet<>();
		itHalfSet.add(itHalf);
		final Term forallTerm1 = SmtUtils.quantifier(script, 1, itHalfSet, forallTermConjunction1);

		// (=> ((and (<= 1 itHalf) (<= itHalf itFinHalf))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term itHalfLeqItFinHalf = script.term("<=", itHalf, itFinHalf);
		final Term forallTerm2Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalf);

		final Term forallTerm2Implication1 = Util.implies(script, forallTerm2Implication1Left, guardOfClosedFormEvenIt);

		// (=> ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1)))) (guard(closedFormOdd(x,
		// 2*itHalf+1))))))
		final Term forallTerm2Implication2 = Util.implies(script, forallTerm1Implication2Left, guardOfClosedFormOddIt);

		final Term forallTermConjunction2 = Util.and(script, forallTerm2Implication1, forallTerm2Implication2);
		final Term forallTerm2 = SmtUtils.quantifier(script, 1, itHalfSet, forallTermConjunction2);

		// (x' = closedFormEven(x,2*itFinHalf))
		final Term xPrimedEven = constructClosedUpdateConstraint(script, loopTransFormula, su.getHavocedVars(),
				closedFormEvenItFin);
		// (x' = closedFormOdd(x,2*itFinHalf+1))
		final Term xPrimedOdd = constructClosedUpdateConstraint(script, loopTransFormula, su.getHavocedVars(),
				closedFormOddItFin);

		// (and (not (guardOfClosedFormEvenItFin)) (forallTerm1) (xPrimedEven))
		final List<Term> innerConjuncts1 = new ArrayList<>();
		innerConjuncts1.add(itFinHalfGreater0);
		innerConjuncts1.add(guardTf.getFormula());
		if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
			innerConjuncts1.add(Util.not(script, guardOfClosedFormEvenItFin));
		}
		innerConjuncts1.add(forallTerm1);
		innerConjuncts1.add(xPrimedEven);
		final Term innerConjunction1 = SmtUtils.and(script, innerConjuncts1);

		// (and (>= itFinHalf 0) (not (guardOfClosedFormOddItFin) (forallTerm2)) (xPrimedOdd))
		final Term itFinHalfGeq0 = script.term(">=", itFinHalf, script.numeral(BigInteger.ZERO));

		final List<Term> innerConjuncts2 = new ArrayList<>();
		innerConjuncts2.add(itFinHalfGeq0);
		innerConjuncts2.add(guardTf.getFormula());
		if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
			innerConjuncts2.add(Util.not(script, guardOfClosedFormOddItFin));
		}
		innerConjuncts2.add(forallTerm2);
		innerConjuncts2.add(xPrimedOdd);

		final Term innerConjunction2 = SmtUtils.and(script, innerConjuncts2);

		final Term middleDisjunction = Util.or(script, firstFinalDisjunctEven, innerConjunction1);

		final Term disjunction = Util.or(script, middleDisjunction, innerConjunction2);

		final Set<TermVariable> itFinHalfSet = new HashSet<>();
		itFinHalfSet.add(itFinHalf);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinHalfSet, disjunction);

		if (quantifyItFinExplicitly) {
			return loopAccelerationTerm;
		} else {
			return disjunction;
		}
	}

	/**
	 * Construct formula that states that all outVars equal the corresponding inVar. Missing inVars are added on-demand.
	 */
	private static Term constructXPrimeEqualsX(final ManagedScript mgdScript,
			final Map<IProgramVar, TermVariable> modifiableInVars, final Map<IProgramVar, TermVariable> outVars) {
		final Term[] xPrimeEqualsXArray = new Term[outVars.size()];
		int k = 0;
		for (final IProgramVar outVar : outVars.keySet()) {
			if (!modifiableInVars.containsKey(outVar)) {
				final TermVariable inVar = mgdScript.constructFreshTermVariable(outVar.getGloballyUniqueId(),
						outVar.getTermVariable().getSort());
				modifiableInVars.put(outVar, inVar);
			}
			xPrimeEqualsXArray[k] = mgdScript.term(null, "=", outVars.get(outVar), modifiableInVars.get(outVar));
			k = k + 1;
		}
		final Term xPrimeEqualsX = Util.and(mgdScript.getScript(), xPrimeEqualsXArray);
		return xPrimeEqualsX;
	}

	/**
	 * Method to check correctness of quantifier elimination.
	 */
	private static boolean checkCorrectnessOfQuantifierElimination(final ILogger logger, final Script script,
			final Term quantifiedFormula, final Term formulaWithoutQuantifiers) {
		if (Util.checkSat(script,
				Util.and(script, quantifiedFormula, Util.not(script, formulaWithoutQuantifiers))) == LBool.SAT) {
			throw new AssertionError("Something went wrong in quantifier elimination.");
		} else if (Util.checkSat(script,
				Util.and(script, quantifiedFormula, Util.not(script, formulaWithoutQuantifiers))) == LBool.UNKNOWN) {
			logger.warn("Unable to prove correctness of quantifier elimination.");
		}
		if (Util.checkSat(script,
				Util.and(script, formulaWithoutQuantifiers, Util.not(script, quantifiedFormula))) == LBool.SAT) {
			throw new AssertionError("Something went wrong in quantifier elimination.");
		} else if (Util.checkSat(script,
				Util.and(script, formulaWithoutQuantifiers, Util.not(script, quantifiedFormula))) == LBool.UNKNOWN) {
			logger.warn("Unable to prove correctness of quantifier elimination.");
		}
		return true;
	}

	/**
	 * The resulting acceleration formula describes a subset R* of a reflexive transitive closure: ((({expr} x S_V,\mu)
	 * \cap [[st]])* \cap (S_V,\mu x {!expr})). This method tests the correctness of the acceleration formula. It checks
	 * whether {(x,x') | x = x' and not guard(x')}, {(x,x') | loopTransFormula(x,x') and not guard(closedForm(x,1))},
	 * {(x,x') | sequentialComposition(x,x') and not guard(closedForm(x,2)} are subsets of R*. It also checks whether a
	 * "havoc" of all assigned variables is a superset of R*.
	 */
	private static boolean checkPropertiesOfLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final UnmodifiableTransFormula loopTransFormula, final Map<IProgramVar, TermVariable> inVars,
			final Term loopAccelerationTerm, final UnmodifiableTransFormula guardTf, final Term xPrimeEqualsX,
			final Term guardOfClosedFormEven, final Term guardOfClosedFormOdd, final TermVariable it,
			final boolean restrictedVersion) {
		final Script script = mgdScript.getScript();

		final Term nnf =
				new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = PartialQuantifierElimination.eliminateCompat(services,
				mgdScript, true, PqeTechniques.ALL, SimplificationTechnique.NONE, nnf);
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

		// Check correctness of quantifier elimination.
		assert checkCorrectnessOfQuantifierElimination(logger, script, loopAccelerationTerm, simplified);

		// Check reflexivity.
		// Check: (x = x') and not (guard(x)) and not (loopAccelerationFormula(x,x')) is unsat.
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term notLoopAccFormula = Util.not(script, simplified);
		// final Term notLoopAccFormula = Util.not(script, loopAccelerationFormula.getFormula());
		if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove reflexivity of computed reflexive-transitive closure.");
		}
		if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.SAT) {
			throw new AssertionError("Computed reflexive-transitive closure is not reflexive. Something went wrong"
					+ "in computation of loop acceleration formula.");
		}

		// Check whether relation itself is subset of reflexive transitive closure.
		// Check: loopTransFormula(x,x') and not (guard(closedForm(x,1))) and not (loopAccelerationFormula(x,x'))
		// is unsat.
		final Map<TermVariable, ConstantTerm> substitutionMapping1 = new HashMap<>();
		if (restrictedVersion) {
			substitutionMapping1.put(it, (ConstantTerm) script.numeral(BigInteger.ONE));
		} else {
			substitutionMapping1.put(it, (ConstantTerm) script.numeral(BigInteger.ZERO));
		}
		final Term guardOfClosedForm1 = Substitution.apply(mgdScript, substitutionMapping1, guardOfClosedFormOdd);
		final Term notGuardOfClosedForm1 = Util.not(script, guardOfClosedForm1);

		if (Util.checkSat(script, Util.and(script, loopTransFormula.getFormula(), notGuardOfClosedForm1,
				notLoopAccFormula)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove that computed reflexive-transitive closure contains relation itself.");
		}
		if (Util.checkSat(script, Util.and(script, loopTransFormula.getFormula(), notGuardOfClosedForm1,
				notLoopAccFormula)) == LBool.SAT) {
			throw new AssertionError("Computed reflexive-transitive closure does not contain relation itself."
					+ "Something went wrong in computation of loop acceleration formula.");
		}

		// Check whether sequential composition of relation with itself is subset of reflexive transitive closure
		// Check: sequCompo(x,x') and not (guard(closedForm(x,2)))
		// and not (loopAccelerationFormula(x,x')) is unsat.
		final List<UnmodifiableTransFormula> loopTransFormulaList = new ArrayList<>();
		loopTransFormulaList.add(loopTransFormula);
		loopTransFormulaList.add(loopTransFormula);
		final UnmodifiableTransFormula sequentialComposition =
				TransFormulaUtils.sequentialComposition(logger, services, mgdScript, true, true, false,
						XnfConversionTechnique.BDD_BASED, SimplificationTechnique.NONE, loopTransFormulaList);
		final Map<TermVariable, TermVariable> substitutionMappingSc = new HashMap<>();
		for (final IProgramVar iVar : sequentialComposition.getInVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getInVars().get(iVar), inVars.get(iVar));
		}
		for (final IProgramVar iVar : sequentialComposition.getOutVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getOutVars().get(iVar),
					loopTransFormula.getOutVars().get(iVar));
		}
		final Term sequentialCompositionSubst = Substitution.apply(mgdScript, substitutionMappingSc,
				sequentialComposition.getFormula());
		final Map<TermVariable, ConstantTerm> substitutionMapping2 = new HashMap<>();
		if (restrictedVersion) {
			substitutionMapping2.put(it, (ConstantTerm) script.numeral(BigInteger.TWO));
		} else {
			substitutionMapping2.put(it, (ConstantTerm) script.numeral(BigInteger.ONE));
		}
		final PureSubstitution subst2 = new PureSubstitution(script, substitutionMapping2);
		final Term notGuardOfClosedForm2 = Util.not(script, subst2.transform(guardOfClosedFormEven));

		if (Util.checkSat(script, Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2,
				notLoopAccFormula)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove that computed reflexive-transitive closure contains sequential"
					+ "composition of relation with itself.");
		}
		if (Util.checkSat(script,
				Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2, notLoopAccFormula)) == LBool.SAT) {
			throw new AssertionError("Computed reflexive-transitive closure does not contain sequential composition of"
					+ " relation with itself. Something went wrong in computation of loop acceleration formula.");
		}

		// Check whether "havoc" of all variables is superset of reflexive transitive closure.
		// Check: loopAccelerationFormula(x,x') and (not x = x') and (not guard(x) is unsat.
		if (Util.checkSat(script,
				Util.and(script, simplified, Util.not(script, xPrimeEqualsX), notGuard)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove that havoc of all variables is a superset of the reflexive"
					+ "transitive closure.");
		}
		if (Util.checkSat(script,
				Util.and(script, simplified, Util.not(script, xPrimeEqualsX), notGuard)) == LBool.SAT) {
			throw new AssertionError("Havoc of all variables is not a superset of the reflexive transitive closure."
					+ "Something went wrong in computation of loop acceleration formula.");
		}
		return true;
	}

	private static class LinearUpdate {
		Map<TermVariable, AffineTerm> mUpdateMap;
		Set<Term> mReadonlyVariables;
		public LinearUpdate(final Map<TermVariable, AffineTerm> updateMap, final Set<Term> readonlyVariables) {
			super();
			mUpdateMap = updateMap;
			mReadonlyVariables = readonlyVariables;
		}
		public Map<TermVariable, AffineTerm> getUpdateMap() {
			return mUpdateMap;
		}
		public Set<Term> getReadonlyVariables() {
			return mReadonlyVariables;
		}
	}

	public static class JordanLoopAccelerationResult {
		public enum AccelerationStatus {
			SUCCESS, SIMULTANEOUS_UPDATE_FAILED, NONINTEGER_UPDATE, NONLINEAR_UPDATE, UNSUPPORTED_EIGENVALUES,
		};

		private final AccelerationStatus mAccelerationStatus;
		private final String mErrorMessage;
		private final UnmodifiableTransFormula mTransFormula;
		private final JordanLoopAccelerationStatisticsGenerator mJordanLoopAccelerationStatistics;

		public JordanLoopAccelerationResult(final AccelerationStatus accelerationStatus, final String errorMessage,
				final UnmodifiableTransFormula transFormula,
				final JordanLoopAccelerationStatisticsGenerator jordanLoopAccelerationStatistics) {
			super();
			mAccelerationStatus = accelerationStatus;
			mErrorMessage = errorMessage;
			mTransFormula = transFormula;
			mJordanLoopAccelerationStatistics = jordanLoopAccelerationStatistics;
		}

		public AccelerationStatus getAccelerationStatus() {
			return mAccelerationStatus;
		}

		public String getErrorMessage() {
			return mErrorMessage;
		}

		public UnmodifiableTransFormula getTransFormula() {
			return mTransFormula;
		}

		public JordanLoopAccelerationStatisticsGenerator getJordanLoopAccelerationStatistics() {
			return mJordanLoopAccelerationStatistics;
		}


	}
}