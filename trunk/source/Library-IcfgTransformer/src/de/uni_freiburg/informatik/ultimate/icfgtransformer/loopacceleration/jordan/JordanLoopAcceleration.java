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
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.CopyingTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierPushTermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
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
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final ITransformulaTransformer mTransformer;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<OUTLOC> mResult;

	public JordanLoopAcceleration(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final IBacktranslationTracker backtranslationTracker,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mServices = services;
		mTransformer = new JordanLoopAccelerationTransformer(mLogger,
				originalIcfg.getCfgSmtToolkit().getManagedScript(), originalIcfg.getCfgSmtToolkit());
		mResult = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac, backtranslationTracker, outLocationClass,
				newIcfgIdentifier, mTransformer).getResult();
	}

	/**
	 * Loop acceleration for loops with linear updates, where only -1,0,1 are eigenvalues of the update matrix.
	 */
	public static UnmodifiableTransFormula accelerateLoop(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final UnmodifiableTransFormula loopTransFormula) {
		final ILogger logger = services.getLoggingService().getLogger(JordanLoopAcceleration.class);
		final UnmodifiableTransFormula guardTf =
				TransFormulaUtils.computeGuard(loopTransFormula, mgdScript, services, logger);
		logger.info("Guard: " + guardTf);
		final SimultaneousUpdate su = new SimultaneousUpdate(loopTransFormula, mgdScript);

		final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator();

		final boolean itFinAuxVar = true;

		final UnmodifiableTransFormula loopAccelerationFormula = createLoopAccelerationFormulaRestricted(logger,
				services, jlasg, mgdScript, su, loopTransFormula, guardTf, true, itFinAuxVar);

		if (QuantifierUtils.isQuantifierFree(loopAccelerationFormula.getFormula())) {
			jlasg.reportQuantifierFreeResult();
		}
		final String shortDescrption = "Jordan loop acceleration statistics";
		final StatisticsData statistics = new StatisticsData();
		statistics.aggregateBenchmarkData(jlasg);
		final String id = "IcfgTransformer";
		services.getResultService().reportResult(id, new StatisticsResult<>(id, shortDescrption, statistics));

		return loopAccelerationFormula;
	}


	/**
	 * Go through terms, get all variables and create a hash map varMatrixIndex with
	 * variables as key and corresponding matrix index as value to save which column
	 * corresponds to which variable and which row corresponds to which update.
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
	 * Determine the coefficient of termVar in the polynomial polyRhs.
	 */
	private static BigInteger determineCoefficient(final IPolynomialTerm polyRhs, final TermVariable termVar) {
		for (final Monomial monom : polyRhs.getMonomial2Coefficient().keySet()) {
			if (!monom.isLinear()) {
				throw new AssertionError("Some term is not linear.");
			}
			if (monom.getSingleVariable().equals(termVar)) {
				final Rational coefficient = polyRhs.getMonomial2Coefficient().get(monom);
				if (!coefficient.denominator().equals(BigInteger.valueOf(1))) {
					throw new AssertionError("Some coefficient is not integral.");
				}
				return coefficient.numerator();
			}
		}
		return BigInteger.valueOf(0);
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
	 * Computes the closed form, a hashmap mapping a variable to the corresponding
	 * closed form term, out of the closed form matrix.
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
	 * Compute the closed form given the update.
	 */
	private static AbstractMap.SimpleEntry<HashMap<TermVariable, Term>, Boolean> closedForm(
			final ManagedScript mgdScript, final SimultaneousUpdate su, final TermVariable it,
			final TermVariable itHalf, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final boolean itEven,
			final boolean restrictedVersionPossible) {
		// HashMap to get matrix index from TermVariable.
		final HashMap<TermVariable, Integer> varMatrixIndex = determineMatrixIndices(su);
		final int n = varMatrixIndex.size() + 1;

		// Initialize update matrix with identity matrix (every variable assigned to
		// itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.identityMatrix(n);

		if (updateMatrix.smallEigenvalues()[0] && restrictedVersionPossible) {
			final AbstractMap.SimpleEntry<HashMap<TermVariable, Term>, Boolean> result =
					new AbstractMap.SimpleEntry<>(null, false);
			return result;
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

		assert QuadraticMatrix.checkCorrectnessofJordanDecomposition(updateMatrix, modalUpdate, jordanUpdate,
				inverseModalUpdate);

		final Script script = mgdScript.getScript();

		// Compute matrix that represents closed form.
		final AbstractMap.SimpleEntry<PolynomialTermMatrix, Boolean> closedFormMatrix =
				PolynomialTermMatrix.closedFormMatrix(mgdScript, updateMatrix, modalUpdate, jordanUpdate,
						inverseModalUpdate, it, itHalf, itEven, restrictedVersionPossible);
		if (!closedFormMatrix.getValue()) {
			final AbstractMap.SimpleEntry<HashMap<TermVariable, Term>, Boolean> result =
					new AbstractMap.SimpleEntry<>(null, false);
			return result;
		}
		final HashMap<TermVariable, Term> closedForm = matrix2ClosedForm(script, closedFormMatrix.getKey(),
				varMatrixIndex, su,
				inVars, outVars);
		final AbstractMap.SimpleEntry<HashMap<TermVariable, Term>, Boolean> result =
				new AbstractMap.SimpleEntry<>(closedForm, true);
		return result;
	}

	/**
	 * Computes the term guard(closedForm(inVars)).
	 */
	private static Term guardOfClosedForm(final Script script, final Term guardFormula,
			final HashMap<TermVariable, Term> closedForm, final Map<IProgramVar, TermVariable> inVars,
			final HashMap<TermVariable, IProgramVar> inVarsInverted, final Map<IProgramVar, TermVariable> outVars,
			final HashMap<IProgramVar, TermVariable> havocVars) {
		if (guardFormula instanceof TermVariable) {
			// TODO: Use get + null check instead of contains+get
			if (closedForm.containsKey(outVars.get(inVarsInverted.get(guardFormula)))) {
				return closedForm.get(outVars.get(inVarsInverted.get(guardFormula)));
			} else if (havocVars.containsKey(inVarsInverted.get(guardFormula))) {
				return havocVars.get(inVarsInverted.get(guardFormula));
			}
			return guardFormula;
		}
		if (guardFormula instanceof ConstantTerm) {
			return guardFormula;
		}
		final int size = ((ApplicationTerm) guardFormula).getParameters().length;
		final Term[] paramReplaced = new Term[size];
		for (int i = 0; i < size; i++) {
			paramReplaced[i] = guardOfClosedForm(script, ((ApplicationTerm) guardFormula).getParameters()[i],
					closedForm, inVars, inVarsInverted, outVars, havocVars);
		}
		return script.term(((ApplicationTerm) guardFormula).getFunction().getName(), paramReplaced);
	}

	/**
	 * Create the loop acceleration formula.
	 * If -1 is an eigenvalue or there is a Jordan block greater 2 for eigenvalue 1
	 * return JordanLoopAcceleration#createLoopAccelerationFormula.
	 * General formula:
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
			final ILogger logger, final IUltimateServiceProvider services,
			final JordanLoopAccelerationStatisticsGenerator jlasg, final ManagedScript mgdScript,
			final SimultaneousUpdate su, final UnmodifiableTransFormula loopTransFormula,
			final UnmodifiableTransFormula guardTf, final boolean restrictedVersionPossible,
			final boolean itFinAuxVar) {
		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);
		final TermVariable itFin = mgdScript.constructFreshTermVariable("itFin", sort);

		// Create the subformula guard(cf(x,itFin)).
		final Map<IProgramVar, TermVariable> inVars = new HashMap<IProgramVar, TermVariable>(
				loopTransFormula.getInVars());
		final HashMap<TermVariable, IProgramVar> inVarsInverted = new HashMap<>();
		for (final IProgramVar inVar : inVars.keySet()) {
			inVarsInverted.put(inVars.get(inVar), inVar);
		}
		final AbstractMap.SimpleEntry<HashMap<TermVariable, Term>, Boolean> closedFormItFinTuple =
				closedForm(mgdScript, su, itFin, null, loopTransFormula.getInVars(),
				loopTransFormula.getOutVars(), true, restrictedVersionPossible);
		if (!closedFormItFinTuple.getValue()) {
			return createLoopAccelerationFormula(logger, services, jlasg, mgdScript, su, loopTransFormula, guardTf,
					itFinAuxVar);
		}
		final HashMap<TermVariable, Term> closedFormItFin = closedFormItFinTuple.getKey();
		final HashMap<IProgramVar, TermVariable> havocVars = new HashMap<>();
		for (final IProgramVar havocVar : su.getHavocedVars()) {
			havocVars.put(havocVar, mgdScript.variable(havocVar.getTermVariable().getName() + "_h", sort));
		}
		final Set<TermVariable> havocVarSet = new HashSet<>(havocVars.values());
		final Term guardOfClosedFormItFinTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormItFin, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormItFin = SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormItFinTmp);

		// (and (= itFin 0) (not (guard)) (x'=x))
		final Term itFinIs0 = script.term("=", itFin, script.numeral(BigInteger.ZERO));
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term xPrimeEqualsX = constructXPrimeEqualsX(mgdScript, inVars, loopTransFormula.getOutVars());
		final Term finalDisjunct1 = Util.and(script, itFinIs0, notGuard, xPrimeEqualsX);

		// (< itFin 0)
		final Term firstConjunct = script.term(">", itFin, script.numeral(BigInteger.ZERO));

		// (not (guard(closedForm(x, itFin))))
		final Term notGuardOfCf = Util.not(script, guardOfClosedFormItFin);

		// (forall ((it Int)) (=> (and (<= 1 it) (<= it (- itFin 1)))
		// (guard(closedForm(x,it)))))
		final TermVariable it = mgdScript.constructFreshTermVariable("it", sort);
		final Term itGreater1 = script.term("<=", script.numeral(BigInteger.ONE), it);
		final Term itSmallerItFinM1 = script.term("<=", it, script.term("-", itFin, script.numeral(BigInteger.ONE)));
		final HashMap<TermVariable, Term> closedFormIt = closedForm(mgdScript, su, it, null,
				inVars, loopTransFormula.getOutVars(), true, restrictedVersionPossible).getKey();
		final Term guardOfClosedFormItTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormIt, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormIt = SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormItTmp);
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
				j = j + 1;
			} else if (!su.getHavocedVars().contains(var)) {
				closedFormArray[j] =
						script.term("=", loopTransFormula.getOutVars().get(var),
								inVars.get(var));
				j = j + 1;
			}
		}
		Term xPrimed;
		Term conjunction;
		if (j == 0) {
			conjunction = Util.and(script, firstConjunct, notGuardOfCf, guardTf.getFormula(), fourthConjunct);
		} else if (j==1) {
			xPrimed = closedFormArray[0];
			conjunction = Util.and(script, firstConjunct, notGuardOfCf, guardTf.getFormula(), fourthConjunct, xPrimed);
		} else {
			xPrimed = Util.and(script, Arrays.copyOfRange(closedFormArray, 0, j));
			conjunction =
					Util.and(script, firstConjunct, notGuardOfCf, guardTf.getFormula(), fourthConjunct, xPrimed);
		}

		final Term disjunction = Util.or(script, finalDisjunct1, conjunction);

		final Set<TermVariable> itFinSet = new HashSet<>();
		itFinSet.add(itFin);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinSet, disjunction);

		UnmodifiableTransFormula loopAccelerationFormula;

		if (itFinAuxVar) {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
					.transform(disjunction);
			final Term loopAccelerationFormulaWithoutQuantifiers =
					QuantifierPushTermWalker.eliminate(services, mgdScript, true, PqeTechniques.ALL, nnf);
			final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
					mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars,
					loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
					loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
					loopTransFormula.getBranchEncoders(), false);

			tfb.addAuxVar(itFin);
			tfb.setFormula(simplified);
			tfb.setInfeasibility(loopTransFormula.isInfeasible());

			loopAccelerationFormula = tfb.finishConstruction(mgdScript);

			// Check correctness of quantifier elimination.
			assert checkCorrectnessOfQuantifierElimination(logger, script, disjunction, simplified);
		} else {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
					.transform(loopAccelerationTerm);
			final Term loopAccelerationFormulaWithoutQuantifiers =
					QuantifierPushTermWalker.eliminate(services, mgdScript, true, PqeTechniques.ALL, nnf);
			final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
					mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

			final TransFormulaBuilder tfb = new TransFormulaBuilder(loopTransFormula.getInVars(),
					loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
					loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
					loopTransFormula.getBranchEncoders(), loopTransFormula.getAuxVars().isEmpty());
			tfb.setFormula(simplified);
			tfb.setInfeasibility(loopTransFormula.isInfeasible());

			loopAccelerationFormula = tfb.finishConstruction(mgdScript);

			// Quantifier elimination is checked within checkPropertiesOfLoopAccelerationFormula.
		}

		assert checkPropertiesOfLoopAccelerationFormula(logger, services, mgdScript, loopTransFormula,
				loopAccelerationFormula, loopAccelerationTerm, guardTf, xPrimeEqualsX, guardOfClosedFormIt,
				guardOfClosedFormIt, it, true);

		jlasg.reportOneCaseAcceleration();

		return loopAccelerationFormula;
	}

	/**
	 * Create the loop acceleration formula. Used if restricted version fails.
	 * General formula:
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
	private static UnmodifiableTransFormula createLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final JordanLoopAccelerationStatisticsGenerator jlasg,
			final ManagedScript mgdScript, final SimultaneousUpdate su,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final boolean itFinAuxVar) {

		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);

		// (and (= itFinHalf 0) (not (guard)) (x'=x))
		final TermVariable itFinHalf = mgdScript.constructFreshTermVariable("itFinHalf", sort);
		final Term itFinHalfEquals0 = script.term("=", itFinHalf, script.numeral(BigInteger.ZERO));
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Map<IProgramVar, TermVariable> inVars = new HashMap<IProgramVar, TermVariable>(loopTransFormula.getInVars());
		final Term xPrimeEqualsX = constructXPrimeEqualsX(mgdScript, inVars, loopTransFormula.getOutVars());
		final Term firstFinalDisjunctEven = Util.and(script, itFinHalfEquals0, notGuard, xPrimeEqualsX);

		// (> itFinHalf 0)
		final Term itFinHalfGreater0 = script.term(">", itFinHalf, script.numeral(BigInteger.ZERO));

		// (not (guard(closedFormEven(x, 2*itFinHalf))))
		final HashMap<TermVariable, IProgramVar> inVarsInverted = new HashMap<>();
		for (final IProgramVar inVar : inVars.keySet()) {
			inVarsInverted.put(inVars.get(inVar), inVar);
		}

		final HashMap<IProgramVar, TermVariable> havocVars = new HashMap<>();
		for (final IProgramVar havocVar : su.getHavocedVars()) {
			havocVars.put(havocVar, mgdScript.variable(havocVar.getTermVariable().getName() + "_h", sort));
		}
		final Set<TermVariable> havocVarSet = new HashSet<>(havocVars.values());

		final HashMap<TermVariable, Term> closedFormEvenItFin = closedForm(mgdScript, su, null, itFinHalf,
				inVars, loopTransFormula.getOutVars(), true, false).getKey();
		final Term guardOfClosedFormEvenItFinTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormEvenItFin, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormEvenItFin =
				SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormEvenItFinTmp);

		final HashMap<TermVariable, Term> closedFormOddItFin = closedForm(mgdScript, su, null, itFinHalf,
				inVars, loopTransFormula.getOutVars(), false, false).getKey();
		final Term guardOfClosedFormOddItFinTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormOddItFin, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormOddItFin =
				SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormOddItFinTmp);

		// ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
		final TermVariable itHalf = mgdScript.constructFreshTermVariable("itHalf", sort);
		final Term oneLeqItHalf = script.term("<=", script.numeral(BigInteger.ONE), itHalf);
		final Term itHalfLeqItFinHalfM1 =
				script.term("<=", itHalf, script.term("-", itFinHalf, script.numeral(BigInteger.ONE)));
		final Term forallTerm1Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormEven(x, 2*itHalf)))
		final HashMap<TermVariable, Term> closedFormEvenIt = closedForm(mgdScript, su, null, itHalf,
				inVars, loopTransFormula.getOutVars(), true, false).getKey();
		final Term guardOfClosedFormEvenItTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormEvenIt, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormEvenIt = SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormEvenItTmp);

		// (=> ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term forallTerm1Implication1 = Util.implies(script, forallTerm1Implication1Left,
				guardOfClosedFormEvenIt);

		// ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1))))
		final Term zeroLeqItHalf = script.term("<=", script.numeral(BigInteger.ZERO), itHalf);
		final Term forallTerm1Implication2Left = Util.and(script, zeroLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormOdd(x, 2*itHalf+1))
		final HashMap<TermVariable, Term> closedFormOddIt = closedForm(mgdScript, su, null, itHalf,
				inVars, loopTransFormula.getOutVars(), false, false).getKey();
		final Term guardOfClosedFormOddItTmp = guardOfClosedForm(script, guardTf.getFormula(),
				closedFormOddIt, inVars, inVarsInverted, loopTransFormula.getOutVars(), havocVars);
		final Term guardOfClosedFormOddIt = SmtUtils.quantifier(script, 0, havocVarSet, guardOfClosedFormOddItTmp);

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

		final Term forallTerm2Implication1 = Util.implies(script, forallTerm2Implication1Left,
				guardOfClosedFormEvenIt);

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
				closedFormArrayEven[j] = script.term("=", loopTransFormula.getOutVars().get(var), inVars.get(var));
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
				closedFormArrayOdd[i] = script.term("=", loopTransFormula.getOutVars().get(var), inVars.get(var));
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

		// (and (>= itFinHalf 0) (not (guardOfClosedFormOddItFin) (forallTerm2)) (xPrimedOdd))
		final Term itFinHalfGeq0 = script.term(">=", itFinHalf, script.numeral(BigInteger.ZERO));

		final Term innerConjunction2 = Util.and(script, itFinHalfGeq0, guardTf.getFormula(),
				Util.not(script, guardOfClosedFormOddItFin), forallTerm2, xPrimedOdd);

		final Term middleDisjunction = Util.or(script, firstFinalDisjunctEven, innerConjunction1);

		final Term disjunction = Util.or(script, middleDisjunction, innerConjunction2);

		final Set<TermVariable> itFinHalfSet = new HashSet<>();
		itFinHalfSet.add(itFinHalf);
		final Term loopAccelerationTerm = SmtUtils.quantifier(script, 0, itFinHalfSet, disjunction);

		UnmodifiableTransFormula loopAccelerationFormula;

		if (itFinAuxVar) {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
					.transform(disjunction);
			final Term loopAccelerationFormulaWithoutQuantifiers = QuantifierPushTermWalker.eliminate(services, mgdScript,
					true, PqeTechniques.ALL, nnf);
			final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
					mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars,
					loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
					loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
					loopTransFormula.getBranchEncoders(), false);

			tfb.addAuxVar(itFinHalf);
			tfb.setInfeasibility(loopTransFormula.isInfeasible());
			tfb.setFormula(simplified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);

			// Check correctness of quantifier elimination.
			assert checkCorrectnessOfQuantifierElimination(logger, script, disjunction, simplified);
		} else {
			final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
					.transform(loopAccelerationTerm);
			final Term loopAccelerationFormulaWithoutQuantifiers = QuantifierPushTermWalker.eliminate(services, mgdScript,
					true, PqeTechniques.ALL, nnf);
			final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
					mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

			final TransFormulaBuilder tfb = new TransFormulaBuilder(loopTransFormula.getInVars(),
					loopTransFormula.getOutVars(), loopTransFormula.getNonTheoryConsts().isEmpty(),
					loopTransFormula.getNonTheoryConsts(), loopTransFormula.getBranchEncoders().isEmpty(),
					loopTransFormula.getBranchEncoders(), loopTransFormula.getAuxVars().isEmpty());
			tfb.setInfeasibility(loopTransFormula.isInfeasible());
			tfb.setFormula(simplified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);

			// Correctness of quantifier elimination is checked within checkPropertiesOfLoopAccelerationFormula.
		}

		assert checkPropertiesOfLoopAccelerationFormula(logger, services, mgdScript, loopTransFormula,
				loopAccelerationFormula, loopAccelerationTerm, guardTf, xPrimeEqualsX, guardOfClosedFormEvenIt,
				guardOfClosedFormOddIt, itHalf, false);

		jlasg.reportTwoCaseAcceleration();

		return loopAccelerationFormula;
	}

	/**
	 * Construct formula that states that all outVars equal the corresponding inVar.
	 * Missing inVars are added on-demand.
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
		if (Util.checkSat(script, Util.and(script, quantifiedFormula, Util.not(script, formulaWithoutQuantifiers)))
				== LBool.SAT) {
			throw new AssertionError("Something went wrong in quantifier elimination.");
		} else if (Util.checkSat(script, Util.and(script, quantifiedFormula,
				Util.not(script, formulaWithoutQuantifiers))) == LBool.UNKNOWN) {
			logger.warn("Unable to prove correctness of quantifier elimination.");
		}
		if (Util.checkSat(script, Util.and(script, formulaWithoutQuantifiers, Util.not(script, quantifiedFormula)))
				== LBool.SAT) {
			throw new AssertionError("Something went wrong in quantifier elimination.");
		} else if (Util.checkSat(script,
				Util.and(script, formulaWithoutQuantifiers, Util.not(script, quantifiedFormula))) == LBool.UNKNOWN) {
			logger.warn("Unable to prove correctness of quantifier elimination.");
		}
		return true;
	}
	/**
	 * The resulting acceleration formula describes a subset R* of a reflexive transitive closure: ((({expr} x S_V,\mu)
	 * \cap [[st]])* \cap (S_V,\mu x {!expr})). This method tests the correctness of the acceleration formula.
	 * It checks whether {(x,x') | x = x' and not guard(x')},
	 * {(x,x') | loopTransFormula(x,x') and not guard(closedForm(x,1))},
	 * {(x,x') | sequentialComposition(x,x') and not guard(closedForm(x,2)}
	 * are subsets of R*. It also checks whether a
	 * "havoc" of all assigned variables is a superset of R*.
	 */
	private static boolean checkPropertiesOfLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula loopAccelerationFormula,
			final Term loopAccelerationTerm,
			final UnmodifiableTransFormula guardTf, final Term xPrimeEqualsX, final Term guardOfClosedFormEven,
			final Term guardOfClosedFormOdd, final TermVariable it, final boolean restrictedVersion) {
		final Script script = mgdScript.getScript();

		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
				.transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = QuantifierPushTermWalker.eliminate(services, mgdScript,
				true, PqeTechniques.ALL, nnf);
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA);

		// Check correctness of quantifier elimination.
		assert checkCorrectnessOfQuantifierElimination(logger, script, loopAccelerationTerm, simplified);

		// Check reflexivity.
		// Check: (x = x') and not (guard(x)) and not (loopAccelerationFormula(x,x')) is unsat.
		final Term notGuard = Util.not(script, guardTf.getFormula());
		final Term notLoopAccFormula = Util.not(script, simplified);
		// final Term notLoopAccFormula = Util.not(script, loopAccelerationFormula.getFormula());
		if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula))
				== LBool.UNKNOWN) {
			logger.warn("Unable to prove reflexivity of computed reflexive-transitive closure.");
		}
		if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula))
				== LBool.SAT) {
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
		final Substitution subst1 = new Substitution(script, substitutionMapping1);
		final Term guardOfClosedForm1 = subst1.transform(guardOfClosedFormOdd);
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
		final UnmodifiableTransFormula sequentialComposition = TransFormulaUtils.sequentialComposition(logger,
				services, mgdScript, true, true, false, XnfConversionTechnique.BDD_BASED, SimplificationTechnique.NONE,
				loopTransFormulaList);
		final Map<TermVariable, TermVariable> substitutionMappingSc = new HashMap<>();
		for (final IProgramVar iVar : sequentialComposition.getInVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getInVars().get(iVar),
					loopAccelerationFormula.getInVars().get(iVar));
		}
		for (final IProgramVar iVar : sequentialComposition.getOutVars().keySet()) {
			substitutionMappingSc.put(sequentialComposition.getOutVars().get(iVar),
					loopAccelerationFormula.getOutVars().get(iVar));
		}
		final Substitution substSc = new Substitution(script, substitutionMappingSc);
		final Term sequentialCompositionSubst = substSc.transform(sequentialComposition.getFormula());
		final Map<TermVariable, ConstantTerm> substitutionMapping2 = new HashMap<>();
		if (restrictedVersion) {
			substitutionMapping2.put(it, (ConstantTerm) script.numeral(BigInteger.TWO));
		} else {
			substitutionMapping2.put(it, (ConstantTerm) script.numeral(BigInteger.ONE));
		}
		final Substitution subst2 = new Substitution(script, substitutionMapping2);
		final Term notGuardOfClosedForm2 = Util.not(script, subst2.transform(guardOfClosedFormEven));

		if (Util.checkSat(script, Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2,
				 notLoopAccFormula)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove that computed reflexive-transitive closure contains sequential"
					+ "composition of relation with itself.");
		}
		if (Util.checkSat(script, Util.and(script, sequentialCompositionSubst, notGuardOfClosedForm2,
				notLoopAccFormula)) == LBool.SAT) {
			throw new AssertionError("Computed reflexive-transitive closure does not contain sequential composition of"
					+ " relation with itself. Something went wrong in computation of loop acceleration formula.");
		}

		// Check whether "havoc" of all variables is superset of reflexive transitive closure.
		// Check: loopAccelerationFormula(x,x') and (not x = x') and (not guard(x) is unsat.
		if (Util.checkSat(script, Util.and(script, simplified, Util.not(script,
				xPrimeEqualsX), notGuard)) == LBool.UNKNOWN) {
			logger.warn("Unable to prove that havoc of all variables is a superset of the reflexive"
					+ "transitive closure.");
		}
		if (Util.checkSat(script, Util.and(script, simplified, Util.not(script,
				xPrimeEqualsX), notGuard)) == LBool.SAT) {
			throw new AssertionError("Havoc of all variables is not a superset of the reflexive transitive closure."
					+ "Something went wrong in computation of loop acceleration formula.");
		}
		return true;
	}

	private final class JordanLoopAccelerationTransformer extends CopyingTransformulaTransformer {

		public JordanLoopAccelerationTransformer(final ILogger logger, final ManagedScript managedScript,
				final CfgSmtToolkit oldToolkit) {
			super(logger, managedScript, oldToolkit);
		}

		@Override
		public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
				final UnmodifiableTransFormula tf) {
			if (oldEdge.getSource() == oldEdge.getTarget()) {
				// self loop, lets accelerate
				final UnmodifiableTransFormula oldTf = oldEdge.getTransformula();
				final UnmodifiableTransFormula transformedTf =
						accelerateLoop(mServices, mOriginalIcfg.getCfgSmtToolkit().getManagedScript(), oldTf);
				mLogger.info("Accelerated %s with %s", oldTf, transformedTf);
				return new TransformulaTransformationResult(transformedTf);
			}
			return super.transform(oldEdge, tf);
		}
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}