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
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.LoopExtraction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.SimpleLoop;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	final ILogger mLogger;
	final IIcfg<INLOC> mOriginalIcfg;
	final Class<OUTLOC> mOutLocationClass;
	final ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	final String mNewIcfgIdentifier;
	final ITransformulaTransformer mTransformer;
	final IBacktranslationTracker mBacktranslationTracker;
	final IUltimateServiceProvider mServices;

	public JordanLoopAcceleration(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services) {

		// Setup
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mOutLocationClass = outLocationClass;
		mFunLocFac = funLocFac;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mTransformer = transformer;
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;

		accelerateAll();
	}

	private IIcfg<OUTLOC> accelerateAll() {
		final LoopExtraction<INLOC, OUTLOC> loopExtraction = new LoopExtraction<>(mLogger, mOriginalIcfg);
		for (final SimpleLoop loop : loopExtraction.getLoopTransFormulas()) {
			accelerateLoop(mServices, mOriginalIcfg.getCfgSmtToolkit().getManagedScript(), loop.mLoopTransFormula);
		}
		return null;
	}

	public static UnmodifiableTransFormula accelerateLoop(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final UnmodifiableTransFormula loopTransFormula) {
		final ILogger logger = services.getLoggingService().getLogger(JordanLoopAcceleration.class);
		final UnmodifiableTransFormula guardTf = TransFormulaUtils.computeGuard(loopTransFormula, mgdScript, services,
				logger);
		logger.info("Guard: " + guardTf);
		final SimultaneousUpdate su = new SimultaneousUpdate(loopTransFormula, mgdScript);

		// Try loop acceleration formula for eigenvalues only 0 and 1 and no terms like
		// 1/2*n*(n-1).
		// If -1 is an eigenvalue or terms like 1/2*n*(n-1) occur, try other formula.
		// For other formula, quantifier elimination may not work.
		UnmodifiableTransFormula loopAccelerationFormula;
		try {
			loopAccelerationFormula = createLoopAccelerationFormulaRestricted(services, mgdScript, su, loopTransFormula,
					guardTf);
		} catch (final AssertionError e) {
			loopAccelerationFormula = createLoopAccelerationFormula(services, mgdScript, su, loopTransFormula, guardTf);
		}
		
		// UnmodifiableTransFormula loopAccelerationFormula = createLoopAccelerationFormula(mMgdScript, su, loopTransFormula, guardTf);
		
		return loopAccelerationFormula;
	}

	/**
	 * Go through terms, get all variables and create a hash map varMatrixIndex with
	 * variables as key and corresponding matrix index as value to save which column
	 * corresponds to which variable and which row corresponds to which update.
	 *
	 * @param su
	 * @return
	 */
	private static HashMap<TermVariable, Integer> determineMatrixIndices(final SimultaneousUpdate su) {
		final HashMap<TermVariable, Integer> varMatrixIndex = new HashMap<>();
		int i = -1;
		for (final IProgramVar updatedVar : su.getUpdatedVars().keySet()) {
			if (!varMatrixIndex.containsKey(updatedVar.getTermVariable())) {
				i = i + 1;
				// add all updated variables.
				varMatrixIndex.put(updatedVar.getTermVariable(), i);
			}
			// add all not updated variables.
			final TermVariable[] variables = su.getUpdatedVars().get(updatedVar).getFreeVars();
			for (final TermVariable var : variables) {
				if (!varMatrixIndex.containsKey(var)) {
					i = i + 1;
					varMatrixIndex.put(var, i);
				}
			}
		}
		return varMatrixIndex;
	}

	/**
	 * Fills the row corresponding to variable of the updateMatrix where variable is
	 * updated with polyRhs.
	 *
	 * @param updateMatrix
	 * @param varMatrixIndex
	 * @param polyRhs
	 * @param variable
	 */
	private static void fillMatrixRow(final QuadraticMatrix updateMatrix,
			final HashMap<TermVariable, Integer> varMatrixIndex, final IPolynomialTerm polyRhs,
			final IProgramVar variable) {

		final int n = updateMatrix.getDimension() - 1;
		updateMatrix.setEntry(n, n, BigInteger.valueOf(1));
		// Set diagonal entry to 0 for case variable assignment does not depend on
		// variable itself
		// (matrix was initialized as identity matrix).
		updateMatrix.setEntry(varMatrixIndex.get(variable.getTermVariable()),
				varMatrixIndex.get(variable.getTermVariable()), BigInteger.valueOf(0));

		// Fill row.
		for (final TermVariable termVar : varMatrixIndex.keySet()) {
			updateMatrix.setEntry(varMatrixIndex.get(variable.getTermVariable()), varMatrixIndex.get(termVar),
					determineCoefficient(polyRhs, termVar));
			updateMatrix.setEntry(varMatrixIndex.get(variable.getTermVariable()), n, determineConstant(polyRhs));
		}
	}

	/**
	 *
	 * @param polyRhs
	 * @param termVar
	 * @return coefficient of termVar in the polynomial polyRhs.
	 */
	private static BigInteger determineCoefficient(final IPolynomialTerm polyRhs, final TermVariable termVar) {
		for (final Monomial monom : polyRhs.getMonomial2Coefficient().keySet()) {
			if (!(monom.isLinear())) {
				throw new AssertionError("Some term is not linear.");
			}
			if (monom.getSingleVariable().equals(termVar)) {
				final Rational coefficient = polyRhs.getMonomial2Coefficient().get(monom);
				if (!(coefficient.denominator().equals(BigInteger.valueOf(1)))) {
					throw new AssertionError("Some coefficient is not integral.");
				}
				return coefficient.numerator();
			}
		}
		return BigInteger.valueOf(0);
	}

	/**
	 * @param polyRhs
	 * @return constant term of polynomial polyRhs.
	 */
	private static BigInteger determineConstant(final IPolynomialTerm polyRhs) {
		final Rational constant = polyRhs.getConstant();
		if (!(constant.denominator().equals(BigInteger.valueOf(1)))) {
			throw new AssertionError("Constant in some term is not integral.");
		}
		return constant.numerator();
	}

	/**
	 * Computes the closed form, a hashmap mapping a variable to the corresponding
	 * closed form term, out of the closed form matrix.
	 *
	 * @param script
	 * @param closedFormMatrix
	 * @param varMatrixIndex
	 * @param su
	 * @param inVars
	 * @param outVars
	 * @return
	 */
	private static HashMap<TermVariable, Term> matrix2ClosedForm(final Script script,
			final PolynomialTermMatrix closedFormMatrix, final HashMap<TermVariable, Integer> varMatrixIndex,
			final SimultaneousUpdate su, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		final HashMap<TermVariable, IProgramVar> termVar2IProgramVar = new HashMap<>();
		for (final IProgramVar inVar : inVars.keySet()) {
			termVar2IProgramVar.put(inVar.getTermVariable(), inVar);
		}
		// Array to get TermVariable from matrix index.
		final TermVariable[] updatedVars = new TermVariable[varMatrixIndex.size()];
		for (final TermVariable var : varMatrixIndex.keySet()) {
			updatedVars[varMatrixIndex.get(var)] = var;
		}
		final int n = closedFormMatrix.getDimension();
		final HashMap<TermVariable, Term> closedForm = new HashMap<>();
		for (final IProgramVar iVar : su.getUpdatedVars().keySet()) {
			final int varIndex = varMatrixIndex.get(iVar.getTermVariable());
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
						summands[current] = inVars.get(termVar2IProgramVar.get(updatedVars[j]));
					} else {
						summands[current] = script.term("*", closedFormMatrix.getEntry(varIndex, j).toTerm(script),
								inVars.get(termVar2IProgramVar.get(updatedVars[j])));
					}
				} else {
					summands[current] = script.term("*", closedFormMatrix.getEntry(varIndex, j).toTerm(script),
							inVars.get(termVar2IProgramVar.get(updatedVars[j])));
				}
				current = current + 1;
			}
			// Add constant term if it is not zero.
			if (closedFormMatrix.getEntry(varIndex, n - 1).isConstant()) {
				final Rational entryRational = closedFormMatrix.getEntry(varIndex, n - 1).getConstant();
				if (entryRational.numerator().intValue() != 0) {
					summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(script);
					current = current + 1;
				}
			} else {
				summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(script);
				current = current + 1;
			}
			Term sum = script.numeral(BigInteger.ZERO);
			if (current == 0) {
				sum = script.numeral(BigInteger.ZERO);
			} else if (current == 1) {
				sum = summands[0];
			} else {
				sum = script.term("+", Arrays.copyOfRange(summands, 0, current));
			}
			closedForm.put(outVars.get(iVar), sum);
		}
		return closedForm;
	}

	/**
	 * Compute the closed form given the update. Use this method only if -1 is not
	 * an eigenvalue of the update matrix.
	 *
	 * @param mgdScript
	 * @param su
	 * @param it
	 * @param inVars
	 * @param outVars
	 * @return
	 */
	private static HashMap<TermVariable, Term> closedForm(final ManagedScript mgdScript, final SimultaneousUpdate su,
			final TermVariable it, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		if (!su.getHavocedVars().isEmpty()) {
			throw new AssertionError("Non-deterministically assigned variable found.");
		}

		// HashMap to get matrix index from TermVariable.
		final HashMap<TermVariable, Integer> varMatrixIndex = determineMatrixIndices(su);
		final int n = varMatrixIndex.size() + 1;

		// Initialize update matrix with identity matrix (every variable assigned to
		// itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.identityMatrix(n);

		if (updateMatrix.smallEigenvalues()[0]) {
			throw new AssertionError("Do not use this method if -1 is an eigenvalue of the update matrix.");
		}

		// Fill update matrix.
		for (final Entry<IProgramVar, Term> update : su.getUpdatedVars().entrySet()) {
			final IPolynomialTerm polyRhs = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
					.transform(update.getValue());

			fillMatrixRow(updateMatrix, varMatrixIndex, polyRhs, update.getKey());
		}

		// Compute Jordan decomposition.
		final QuadraticMatrix jordanUpdate = updateMatrix.jordanMatrix();
		final RationalMatrix modalUpdate = QuadraticMatrix.modalMatrix(updateMatrix, jordanUpdate);
		final RationalMatrix inverseModalUpdate = RationalMatrix.inverse(modalUpdate);
		QuadraticMatrix.checkCorrectnessofJordanDecomposition(updateMatrix, modalUpdate, jordanUpdate,
				inverseModalUpdate);

		final Script script = mgdScript.getScript();

		// Compute matrix that represents closed form.
		final PolynomialTermMatrix closedFormMatrix = PolynomialTermMatrix.closedFormMatrix(mgdScript, updateMatrix,
				modalUpdate, jordanUpdate, inverseModalUpdate, it);
		final HashMap<TermVariable, Term> closedForm = matrix2ClosedForm(script, closedFormMatrix, varMatrixIndex, su,
				inVars, outVars);
		return closedForm;
	}

	/**
	 * Compute the closed form given the update. Use this method if -1 is an
	 * eigenvalue of the update matrix.
	 *
	 * @param mgdScript
	 * @param su
	 * @param itHalf
	 * @param nEven
	 * @param inVars
	 * @param outVars
	 * @return
	 */
	private static HashMap<TermVariable, Term> closedForm(final ManagedScript mgdScript, final SimultaneousUpdate su,
			final TermVariable itHalf, final boolean nEven, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		if (!su.getHavocedVars().isEmpty()) {
			throw new AssertionError("Non-deterministically assigned variable found.");
		}

		// HashMap to get matrix index from TermVariable.
		final HashMap<TermVariable, Integer> varMatrixIndex = determineMatrixIndices(su);
		final int n = varMatrixIndex.size() + 1;

		// Initialize update matrix with identity matrix (every variable assigned to
		// itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.identityMatrix(n);

		// Fill update matrix.
		for (final Entry<IProgramVar, Term> update : su.getUpdatedVars().entrySet()) {
			final IPolynomialTerm polyRhs = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
					.transform(update.getValue());

			fillMatrixRow(updateMatrix, varMatrixIndex, polyRhs, update.getKey());
		}

		// Compute Jordan decomposition.
		final QuadraticMatrix jordanUpdate = updateMatrix.jordanMatrix();
		final RationalMatrix modalUpdate = QuadraticMatrix.modalMatrix(updateMatrix, jordanUpdate);
		final RationalMatrix inverseModalUpdate = RationalMatrix.inverse(modalUpdate);
		QuadraticMatrix.checkCorrectnessofJordanDecomposition(updateMatrix, modalUpdate, jordanUpdate,
				inverseModalUpdate);

		final Script script = mgdScript.getScript();

		// Compute matrix that represents closed form.
		if (nEven) {
			final PolynomialTermMatrix closedFormEvenMatrix = PolynomialTermMatrix.closedFormMatrix(mgdScript,
					updateMatrix, modalUpdate, jordanUpdate, inverseModalUpdate, itHalf, true);
			final HashMap<TermVariable, Term> closedFormEven = matrix2ClosedForm(script, closedFormEvenMatrix,
					varMatrixIndex, su, inVars, outVars);
			return closedFormEven;
		} else {
			final PolynomialTermMatrix closedFormOddMatrix = PolynomialTermMatrix.closedFormMatrix(mgdScript,
					updateMatrix, modalUpdate, jordanUpdate, inverseModalUpdate, itHalf, false);
			final HashMap<TermVariable, Term> closedFormOdd = matrix2ClosedForm(script, closedFormOddMatrix,
					varMatrixIndex, su, inVars, outVars);
			return closedFormOdd;
		}
	}

	/**
	 * Computes the term guard(closedForm(inVars)).
	 *
	 * @param script
	 * @param guardFormula
	 * @param closedForm
	 * @param inVars
	 * @param inVarsInverted
	 * @param outVars
	 * @return
	 */
	private static Term guardOfClosedForm(final Script script, final Term guardFormula,
			final HashMap<TermVariable, Term> closedForm, final Map<IProgramVar, TermVariable> inVars,
			final HashMap<TermVariable, IProgramVar> inVarsInverted, final Map<IProgramVar, TermVariable> outVars) {
		if (guardFormula instanceof TermVariable) {
			if (closedForm.containsKey(outVars.get(inVarsInverted.get(guardFormula)))) {
				return closedForm.get(outVars.get(inVarsInverted.get(guardFormula)));
			} else {
				return guardFormula;
			}
		} else {
			if (guardFormula instanceof ConstantTerm) {
				return guardFormula;
			} else {
				final int size = ((ApplicationTerm) guardFormula).getParameters().length;
				final Term[] paramReplaced = new Term[size];
				for (int i = 0; i < size; i++) {
					paramReplaced[i] = guardOfClosedForm(script, ((ApplicationTerm) guardFormula).getParameters()[i],
							closedForm, inVars, inVarsInverted, outVars);
				}
				return script.term(((ApplicationTerm) guardFormula).getFunction().getName(), paramReplaced);
			}
		}
	}

	/**
	 * Create the loop acceleration formula. Use this method only if -1 is not an
	 * eigenvalue of the update matrix. General formula:
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
	private static UnmodifiableTransFormula createLoopAccelerationFormulaRestricted(
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf) {
		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);
		final TermVariable itFin = mgdScript.variable("itFin", sort);

		// Create the subformula guard(cf(x,itFin)).
		final Map<IProgramVar, TermVariable> inVars = loopTransFormula.getInVars();
		final HashMap<TermVariable, IProgramVar> inVarsInverted = new HashMap<>();
		for (final IProgramVar inVar : inVars.keySet()) {
			inVarsInverted.put(inVars.get(inVar), inVar);
		}
		final HashMap<TermVariable, Term> closedFormItFin = closedForm(mgdScript, su, itFin,
				loopTransFormula.getInVars(), loopTransFormula.getOutVars());
		final Term guardOfClosedFormItFin = guardOfClosedForm(script, guardTf.getFormula(), closedFormItFin, inVars,
				inVarsInverted, loopTransFormula.getOutVars());

		// (and (= itFin 0) (not (guard)) (x'=x))
		final Term itFinIs0 = script.term("=", itFin, script.numeral(BigInteger.ZERO));
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term[] xPrimeEqualsXArray = new Term[loopTransFormula.getOutVars().size()];
		int k = 0;
		for (final IProgramVar outVar : loopTransFormula.getOutVars().keySet()) {
			if (loopTransFormula.getInVars().containsKey(outVar)) {
				xPrimeEqualsXArray[k] = script.term("=", loopTransFormula.getOutVars().get(outVar), inVars.get(outVar));
				k = k + 1;
			} else {
				throw new AssertionError("Could not find inVar for every outVar. Term (x'=x) cannot be constructed.");
			}
		}
		final Term xPrimeEqualsX = Util.and(script, xPrimeEqualsXArray);
		final Term finalDisjunct1 = Util.and(script, itFinIs0, notGuard, xPrimeEqualsX);

		// (< itFin 0)
		final Term firstConjunct = script.term(">", itFin, script.numeral(BigInteger.ZERO));

		// (not (guard(closedForm(x, itFin))))
		final Term notGuardOfCf = Util.not(script, guardOfClosedFormItFin);

		// (forall ((it Int)) (=> (and (<= 1 it) (<= it (- itFin 1)))
		// (guard(closedForm(x,it)))))
		final TermVariable it = mgdScript.variable("it", sort);
		final Term itGreater1 = script.term("<=", script.numeral(BigInteger.ONE), it);
		final Term itSmallerItFinM1 = script.term("<=", it, script.term("-", itFin, script.numeral(BigInteger.ONE)));
		final HashMap<TermVariable, Term> closedFormIt = closedForm(mgdScript, su, it, loopTransFormula.getInVars(),
				loopTransFormula.getOutVars());
		final Term guardOfClosedFormIt = guardOfClosedForm(script, guardTf.getFormula(), closedFormIt, inVars,
				inVarsInverted, loopTransFormula.getOutVars());
		final Term leftSideOfImpl = Util.and(script, itGreater1, itSmallerItFinM1);
		final Term implication = Util.implies(script, leftSideOfImpl, guardOfClosedFormIt);
		final Set<TermVariable> itSet = new HashSet<>();
		itSet.add(it);
		final Term fourthConjunct = SmtUtils.quantifier(script, 1, itSet, implication);

		final int numbOfVars = loopTransFormula.getOutVars().size();
		final Term[] closedFormArray = new Term[numbOfVars];
		int j = 0;
		for (final IProgramVar var : loopTransFormula.getOutVars().keySet()) {
			if (closedFormItFin.containsKey(loopTransFormula.getOutVars().get(var))) {
				closedFormArray[j] = script.term("=", loopTransFormula.getOutVars().get(var),
						closedFormItFin.get(loopTransFormula.getOutVars().get(var)));
			} else {
				closedFormArray[j] = script.term("=", loopTransFormula.getOutVars().get(var),
						loopTransFormula.getInVars().get(var));
			}
			j = j + 1;
		}
		Term xPrimed = closedFormArray[0];
		if (closedFormArray.length > 1) {
			xPrimed = Util.and(script, closedFormArray);
		}

		final Term conjunction = Util.and(script, firstConjunct, notGuardOfCf, guardTf.getFormula(), fourthConjunct,
				xPrimed);

		final Term disjunction = Util.or(script, finalDisjunct1, conjunction);

		final Set<TermVariable> itFinSet = new HashSet<>();
		itFinSet.add(itFin);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinSet, disjunction);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
				.transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = QuantifierPusher.eliminate(services, mgdScript, true,
				PqeTechniques.ALL, nnf);
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

		final TransFormulaBuilder tfb = new TransFormulaBuilder(loopTransFormula.getInVars(),
				loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
				loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
				loopTransFormula.getBranchEncoders(), loopTransFormula.getAuxVars().isEmpty());

		tfb.setFormula(simplified);
		tfb.setInfeasibility(loopTransFormula.isInfeasible());

		final UnmodifiableTransFormula loopAccelerationFormula = tfb.finishConstruction(mgdScript);
		
		checkPropertiesOfLoopAccelerationFormulaRestricted(mgdScript, loopTransFormula, loopAccelerationFormula, guardTf,
				xPrimeEqualsX, guardOfClosedFormIt, it);
		
		return loopAccelerationFormula;
	}

	/**
	 * Create the loop acceleration formula. Use this method if -1 is an eigenvalue
	 * of the update matrix. General formula:
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
	private static UnmodifiableTransFormula createLoopAccelerationFormula(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final SimultaneousUpdate su, final UnmodifiableTransFormula loopTransFormula,
			final UnmodifiableTransFormula guardTf) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(loopTransFormula.getInVars(),
				loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
				loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
				loopTransFormula.getBranchEncoders(), loopTransFormula.getAuxVars().isEmpty());

		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);

		// (and (= itFinHalf 0) (not (guard)) (x'=x))
		final TermVariable itFinHalf = mgdScript.variable("itFinHalf", sort);
		final Term itFinHalfEquals0 = script.term("=", itFinHalf, script.numeral(BigInteger.ZERO));
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term[] xPrimeEqualsXArray = new Term[loopTransFormula.getOutVars().size()];
		int k = 0;
		for (final IProgramVar outVar : loopTransFormula.getOutVars().keySet()) {
			if (loopTransFormula.getInVars().containsKey(outVar)) {
				xPrimeEqualsXArray[k] = script.term("=", loopTransFormula.getOutVars().get(outVar),
						loopTransFormula.getInVars().get(outVar));
				k = k + 1;
			} else {
				throw new AssertionError("Could not find inVar for every outVar. Term (x'=x) cannot be constructed.");
			}
		}
		final Term xPrimeEqualsX = Util.and(script, xPrimeEqualsXArray);
		final Term firstFinalDisjunctEven = Util.and(script, itFinHalfEquals0, notGuard, xPrimeEqualsX);

		// (> itFinHalf 0)
		final Term itFinHalfGreater0 = script.term(">", itFinHalf, script.numeral(BigInteger.ZERO));

		// (not (guard(closedFormEven(x, 2*itFinHalf))))
		final Map<IProgramVar, TermVariable> inVars = loopTransFormula.getInVars();
		final HashMap<TermVariable, IProgramVar> inVarsInverted = new HashMap<>();
		for (final IProgramVar inVar : inVars.keySet()) {
			inVarsInverted.put(inVars.get(inVar), inVar);
		}
		final HashMap<TermVariable, Term> closedFormEvenItFin = closedForm(mgdScript, su, itFinHalf, true,
				loopTransFormula.getInVars(), loopTransFormula.getOutVars());
		final Term guardOfClosedFormEvenItFin = guardOfClosedForm(script, guardTf.getFormula(), closedFormEvenItFin,
				inVars, inVarsInverted, loopTransFormula.getOutVars());
		
		final HashMap<TermVariable, Term> closedFormOddItFin = closedForm(mgdScript, su, itFinHalf, false,
				loopTransFormula.getInVars(), loopTransFormula.getOutVars());
		final Term guardOfClosedFormOddItFin = guardOfClosedForm(script, guardTf.getFormula(), closedFormOddItFin,
				inVars, inVarsInverted, loopTransFormula.getOutVars());

		// ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
		final TermVariable itHalf = mgdScript.variable("itHalf", sort);
		final Term oneLeqItHalf = script.term("<=", script.numeral(BigInteger.ONE), itHalf);
		final Term itHalfLeqItFinHalfM1 = script.term("<=", itHalf,
				script.term("-", itFinHalf, script.numeral(BigInteger.ONE)));
		final Term forallTerm1Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormEven(x, 2*itHalf)))
		final HashMap<TermVariable, Term> closedFormEvenIt = closedForm(mgdScript, su, itHalf, true,
				loopTransFormula.getInVars(), loopTransFormula.getOutVars());
		final Term guardOfClosedFormEvenIt = guardOfClosedForm(script, guardTf.getFormula(), closedFormEvenIt, inVars,
				inVarsInverted, loopTransFormula.getOutVars());

		// (=> ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term forallTerm1Implication1 = Util.implies(script, forallTerm1Implication1Left, guardOfClosedFormEvenIt);

		// ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1))))
		final Term zeroLeqItHalf = script.term("<=", script.numeral(BigInteger.ZERO), itHalf);
		final Term forallTerm1Implication2Left = Util.and(script, zeroLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormOdd(x, 2*itHalf+1))
		final HashMap<TermVariable, Term> closedFormOddIt = closedForm(mgdScript, su, itHalf, false,
				loopTransFormula.getInVars(), loopTransFormula.getOutVars());
		final Term guardOfClosedFormOddIt = guardOfClosedForm(script, guardTf.getFormula(), closedFormOddIt, inVars,
				inVarsInverted, loopTransFormula.getOutVars());

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
		final int numbOfVars = loopTransFormula.getOutVars().size();
		final Term[] closedFormArrayEven = new Term[numbOfVars];
		int j = 0;
		for (final IProgramVar var : loopTransFormula.getOutVars().keySet()) {
			if (closedFormEvenItFin.containsKey(loopTransFormula.getOutVars().get(var))) {
				closedFormArrayEven[j] = script.term("=", loopTransFormula.getOutVars().get(var),
						closedFormEvenItFin.get(loopTransFormula.getOutVars().get(var)));
			} else {
				closedFormArrayEven[j] = script.term("=", loopTransFormula.getOutVars().get(var),
						loopTransFormula.getInVars().get(var));
			}
			j = j + 1;
		}
		Term xPrimedEven = closedFormArrayEven[0];
		if (closedFormArrayEven.length > 1) {
			xPrimedEven = Util.and(script, closedFormArrayEven);
		}

		// (x' = closedFormOdd(x,2*itFinHalf+1))
		final Term[] closedFormArrayOdd = new Term[numbOfVars];
		int i = 0;
		for (final IProgramVar var : loopTransFormula.getOutVars().keySet()) {
			if (closedFormOddItFin.containsKey(loopTransFormula.getOutVars().get(var))) {
				closedFormArrayOdd[i] = script.term("=", loopTransFormula.getOutVars().get(var),
						closedFormOddItFin.get(loopTransFormula.getOutVars().get(var)));
			} else {
				closedFormArrayOdd[i] = script.term("=", loopTransFormula.getOutVars().get(var),
						loopTransFormula.getInVars().get(var));
			}
			i = i + 1;
		}
		Term xPrimedOdd = closedFormArrayOdd[0];
		if (closedFormArrayOdd.length > 1) {
			xPrimedOdd = Util.and(script, closedFormArrayOdd);
		}

		// (and (not (guardOfClosedFormEvenItFin)) (forallTerm1) (xPrimedEven))
		final Term innerConjunction1 = Util.and(script, itFinHalfGreater0, guardTf.getFormula(),
				Util.not(script, guardOfClosedFormEvenItFin), forallTerm1, xPrimedEven);

		// (and (not (guardOfClosedFormOddItFin) (forallTerm2)) (xPrimedOdd))
		final Term innerConjunction2 = Util.and(script, guardTf.getFormula(),
				Util.not(script, guardOfClosedFormOddItFin), forallTerm2, xPrimedOdd);

		final Term middleDisjunction = Util.or(script, firstFinalDisjunctEven, innerConjunction1);

		final Term disjunction = Util.or(script, middleDisjunction, innerConjunction2);

		final Set<TermVariable> itFinHalfSet = new HashSet<>();
		itFinHalfSet.add(itFinHalf);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinHalfSet, disjunction);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
				.transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = QuantifierPusher.eliminate(services, mgdScript, true,
				PqeTechniques.ALL, nnf);
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

		tfb.setInfeasibility(loopTransFormula.isInfeasible());

		tfb.setFormula(simplified);
		final UnmodifiableTransFormula loopAccelerationFormula = tfb.finishConstruction(mgdScript);
		
		checkPropertiesOfLoopAccelerationFormula(mgdScript, loopTransFormula, loopAccelerationFormula,
				guardTf, xPrimeEqualsX, guardOfClosedFormEvenIt, guardOfClosedFormOddIt, itHalf);
		
		return loopAccelerationFormula;
	}
	
	/**
	 * The resulting acceleration formula describes a subset R* of the reflexive transitive closure given by a formula
	 * ((x = x' or (exists n, x_1,...,x_n. x R x_1 R x_2 R...R x_n R x')) and not exists x''. x'Rx''). This method tests
	 * the correctness of the acceleration formula. It checks whether
	 * {(x,x') | x = x' and not guard(x')}, {(x,x') | loopTransFormula(x,x') and not guard(closedForm(x,1))},
	 * {(x,x') | sequentialComposition(x,x') and not guard(closedForm(x,2)} are subsets of R*. It also checks whether
	 * a "havoc" of all assigned variables is a superset of R*.
	 * @param mgdScript
	 * @param loopTransFormula
	 * @param loopAccelerationFormula
	 * @param guardTf
	 * @param xPrimeEqualsX
	 * @param guardOfClosedForm
	 * @param it
	 */
	private void checkPropertiesOfLoopAccelerationFormulaRestricted(ManagedScript mgdScript, UnmodifiableTransFormula loopTransFormula,
			UnmodifiableTransFormula loopAccelerationFormula, UnmodifiableTransFormula guardTf, Term xPrimeEqualsX,
			Term guardOfClosedForm, TermVariable it) {
		final Script script = mgdScript.getScript();
		// Check reflexivity.
		// Check: (x = x') and not (guard(x)) and not (loopAccelerationFormula(x,x')) is unsat.
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term notLoopAccFormula = Util.not(script, loopAccelerationFormula.getFormula());
		assert Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.UNSAT;
		
		// Check whether relation itself is subset of reflexive transitive closure.
		// Check: loopTransFormula(x,x') and not (guard(closedForm(x,1))) and not (loopAccelerationFormula(x,x')) is unsat.
		final Map<TermVariable, ConstantTerm> substitutionMapping1 = new HashMap<>();
		substitutionMapping1.put(it, (ConstantTerm) script.numeral(BigInteger.ONE));
		final Substitution subst1 = new Substitution(script, substitutionMapping1);
		final Term notGuardOfClosedForm1 = Util.not(script, subst1.transform(guardOfClosedForm));
		assert Util.checkSat(script, Util.and(script, loopTransFormula.getFormula(), notGuardOfClosedForm1, notLoopAccFormula)) ==
				LBool.UNSAT;
		
		// Check whether sequential composition of relation with itself is subset of reflexive transitive closure.
		// Check: sequCompo(x,x') and not (guard(closedForm(x,2))) and not (loopAccelerationFormula(x,x')) is unsat.
		List<UnmodifiableTransFormula> loopTransFormulaList = new ArrayList<>();
		loopTransFormulaList.add(loopTransFormula);
		loopTransFormulaList.add(loopTransFormula);
		
		UnmodifiableTransFormula sequentialComposition = TransFormulaUtils.sequentialComposition(mLogger,
				mServices, mgdScript, true, true, false, XnfConversionTechnique.BDD_BASED, SimplificationTechnique.NONE,
				loopTransFormulaList);
		final Map<TermVariable, TermVariable> substitutionMappingSc = new HashMap<>();
		for (IProgramVar iVar : sequentialComposition.getInVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getInVars().get(iVar), loopAccelerationFormula.getInVars().get(iVar));
		}
		for (IProgramVar iVar : sequentialComposition.getOutVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getOutVars().get(iVar), loopAccelerationFormula.getOutVars().get(iVar));
		}
		final Substitution substSc = new Substitution(script, substitutionMappingSc);
		final Term sequentialCompositionSubst = substSc.transform(sequentialComposition.getFormula());
		final Map<TermVariable, ConstantTerm> substitutionMapping2 = new HashMap<>();
		substitutionMapping2.put(it, (ConstantTerm) script.numeral(BigInteger.TWO));
		final Substitution subst2 = new Substitution(script, substitutionMapping2);
		final Term notGuardOfClosedForm2 = Util.not(script, subst2.transform(guardOfClosedForm));
		assert Util.checkSat(script, Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2,
				notLoopAccFormula)) == LBool.UNSAT;
		
		// Check whether "havoc" of all variables is superset of reflexive transitive closure.
		// Check: loopAccelerationFormula(x,x') and (not x = x') and (not guard(x) is unsat.
		assert Util.checkSat(script, Util.and(script, loopAccelerationFormula.getFormula(), Util.not(script, 
				xPrimeEqualsX), notGuard)) == LBool.UNSAT;
	}
	
	/**
	 * The resulting acceleration formula describes a subset R* of the reflexive transitive closure given by a formula
	 * ((x = x' or (exists n, x_1,...,x_n. x R x_1 R x_2 R...R x_n R x')) and not exists x''. x'Rx''). This method tests
	 * the correctness of the acceleration formula. It checks whether
	 * {(x,x') | x = x' and not guard(x')}, {(x,x') | loopTransFormula(x,x') and not guard(closedFormOdd(x,1))},
	 * {(x,x') | sequentialComposition(x,x') and not guard(closedFormEven(x,2)} are subsets of R*. It also checks whether
	 * a "havoc" of all assigned variables is a superset of R*.
	 * @param mgdScript
	 * @param loopTransFormula
	 * @param loopAccelerationFormula
	 * @param guardTf
	 * @param xPrimeEqualsX
	 * @param guardOfClosedFormEven
	 * @param guardOfClosedFormOdd
	 * @param itHalf
	 */
	private void checkPropertiesOfLoopAccelerationFormula(ManagedScript mgdScript, UnmodifiableTransFormula loopTransFormula,
			UnmodifiableTransFormula loopAccelerationFormula, UnmodifiableTransFormula guardTf, Term xPrimeEqualsX,
			Term guardOfClosedFormEven, Term guardOfClosedFormOdd, TermVariable itHalf) {
		final Script script = mgdScript.getScript();
		// Check reflexivity.
		// Check: (x = x') and not (guard(x)) and not (loopAccelerationFormula(x,x')) is unsat.
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term notLoopAccFormula = Util.not(script, loopAccelerationFormula.getFormula());
		assert Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.UNSAT;
		
		// Check whether relation itself is subset of reflexive transitive closure.
		// Check: loopTransFormula(x,x') and not (guard(closedFormEven(x,1))) and not (loopAccelerationFormula(x,x')) is unsat.
		final Map<TermVariable, ConstantTerm> substitutionMapping1 = new HashMap<>();
		substitutionMapping1.put(itHalf, (ConstantTerm) script.numeral(BigInteger.ZERO));
		Substitution subst1 = new Substitution(script, substitutionMapping1);
		Term notGuardOfClosedForm1 = Util.not(script, subst1.transform(guardOfClosedFormOdd));
		assert Util.checkSat(script, Util.and(script, loopTransFormula.getFormula(), notGuardOfClosedForm1, notLoopAccFormula)) ==
				LBool.UNSAT;
		
		// Check whether sequential composition of relation with itself is subset of reflexive transitive closure.
		// Check: sequCompo(x,x') and not (guard(closedForm(x,2))) and not (loopAccelerationFormula(x,x')) is unsat.
		List<UnmodifiableTransFormula> loopTransFormulaList = new ArrayList<>();
		loopTransFormulaList.add(loopTransFormula);
		loopTransFormulaList.add(loopTransFormula);
				
		UnmodifiableTransFormula sequentialComposition = TransFormulaUtils.sequentialComposition(mLogger,
				mServices, mgdScript, true, true, false, XnfConversionTechnique.BDD_BASED, SimplificationTechnique.NONE,
				loopTransFormulaList);
		final Map<TermVariable, TermVariable> substitutionMappingSc = new HashMap<>();
		for (IProgramVar iVar : sequentialComposition.getInVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getInVars().get(iVar), loopAccelerationFormula.getInVars().get(iVar));
		}
		for (IProgramVar iVar : sequentialComposition.getOutVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getOutVars().get(iVar), loopAccelerationFormula.getOutVars().get(iVar));
		}
		final Substitution substSc = new Substitution(script, substitutionMappingSc);
		final Term sequentialCompositionSubst = substSc.transform(sequentialComposition.getFormula());
		final Map<TermVariable, ConstantTerm> substitutionMapping2 = new HashMap<>();
		substitutionMapping2.put(itHalf, (ConstantTerm) script.numeral(BigInteger.ONE));
		final Substitution subst2 = new Substitution(script, substitutionMapping2);
		final Term notGuardOfClosedForm2 = Util.not(script, subst2.transform(guardOfClosedFormEven));
		assert Util.checkSat(script, Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2,
				notLoopAccFormula)) == LBool.UNSAT;
		
		// Check whether "havoc" of all variables is superset of reflexive transitive closure.
		// Check: loopAccelerationFormula(x,x') and (not x = x') and (not guard(x) is unsat.
		assert Util.checkSat(script, Util.and(script, loopAccelerationFormula.getFormula(), Util.not(script, 
				xPrimeEqualsX), notGuard)) == LBool.UNSAT;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return null;
	}
}