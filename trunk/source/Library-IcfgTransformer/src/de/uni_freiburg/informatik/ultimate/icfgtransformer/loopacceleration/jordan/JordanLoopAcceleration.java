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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.LoopAccelerationUtils;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanAcceleratedUpdate.LinearUpdate;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult.JordanTransformationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate.SimultaneousUpdateException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdateWithReplacements;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
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
	/**
	 * If set to true, we construct the reflexive, transitive closure, if set to
	 * false, we construct only the transitive closure.
	 */
	private static final boolean REFLEXIVE_TRANSITIVE_CLOSURE = false;

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
		final int numberOfArrayWrites = su.getDeterministicArrayWrites().size();
		final int numberOfHavocedVariables = su.getHavocedVars().size();

		final SimultaneousUpdateWithReplacements suwr = SimultaneousUpdateWithReplacements.replaceArrayIndices(mgdScript, su);

		final Set<Sort> nonIntegerSorts = getNonIntegerSorts(suwr.getDeterministicAssignment().keySet());
		if (!nonIntegerSorts.isEmpty()) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, -1, new NestedMap2<>());
			final String errorMessage = "Some updated variables are of non-integer sorts : " + nonIntegerSorts;
			return new JordanLoopAccelerationResult(JordanLoopAccelerationResult.AccelerationStatus.NONINTEGER_UPDATE,
					errorMessage, null, jlasg);
		}

		final Pair<LinearUpdate, String> pair = extractLinearUpdate(mgdScript, suwr);
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
		final HashMap<Term, Integer> varMatrixIndexMap = JordanAcceleratedUpdate
				.determineMatrixIndices(pair.getFirst());
		final QuadraticMatrix updateMatrix = JordanAcceleratedUpdate.computeUpdateMatrix(pair.getFirst(), varMatrixIndexMap);

		final JordanTransformationResult jordanUpdate = updateMatrix.constructJordanTransformation();

		if (jordanUpdate.getStatus() == JordanTransformationStatus.UNSUPPORTED_EIGENVALUES) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, numberOfReadonlyVariables, new NestedMap2<>());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.UNSUPPORTED_EIGENVALUES, null, null, jlasg);
		}
		assert JordanAcceleratedUpdate.isBlockSizeConsistent(numberOfAssignedVariables, numberOfArrayWrites,
				numberOfReadonlyVariables, jordanUpdate) : "inconsistent blocksize";

		final boolean isAlternatingClosedFormRequired = JordanAcceleratedUpdate
				.isAlternatingClosedFormRequired(jordanUpdate);
		final UnmodifiableTransFormula guardTf =
				TransFormulaUtils.computeGuard(loopTransFormula, mgdScript, services);
		final UnmodifiableTransFormula loopAccelerationFormula = createLoopAccelerationFormula(logger, services,
				mgdScript, su, suwr, pair.getFirst(), varMatrixIndexMap, jordanUpdate, loopTransFormula, guardTf, true,
				quantifyItFinExplicitly, isAlternatingClosedFormRequired);
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
			final SimultaneousUpdateWithReplacements suwr) {
		final Set<TermVariable> termVariablesOfModified = new HashSet<>();
		for (final Entry<IProgramVar, Term> update : suwr.getDeterministicAssignment().entrySet()) {
			termVariablesOfModified.add(update.getKey().getTermVariable());
		}
		for (final IProgramVar pv : suwr.getHavocedVars()) {
			termVariablesOfModified.add(pv.getTermVariable());
		}
		final Set<Term> readonlyVariables = new HashSet<>();
		final Map<TermVariable, AffineTerm> updateMap = new HashMap<>();
		for (final Entry<IProgramVar, Term> update : suwr.getDeterministicAssignment().entrySet()) {
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
		// TODO Matthias: allow also affine terms with polynomials as variables
		for (final Entry<TermVariable, Term> entry : suwr.getIdxRepAssignments().entrySet()) {
			final AffineTerm at = (AffineTerm) new AffineTermTransformer(mgdScript.getScript()).transform(entry.getValue());
			updateMap.put(entry.getKey(), at);
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
	 * Compute the closed form given the update, the update matrix and the corresponding jordan matrix.
	 */
	private static ClosedFormOfUpdate computeClosedFormOfUpdate(final ManagedScript mgdScript,
			final SimultaneousUpdateWithReplacements suwr, final LinearUpdate linearUpdate,
			final HashMap<Term, Integer> varMatrixIndexMap, final JordanTransformationResult jordanUpdate,
			final TermVariable it, final TermVariable itHalf, final Map<IProgramVar, TermVariable> inVars,
			final boolean itEven, final boolean restrictedVersionPossible) {
		final Map<TermVariable, Term> closedFormMapWithoutReplacementTvs;
		final NestedMap2<IProgramVar, ArrayIndex, Term> array2Index2valuesWithoutReplacementTvs;
		{
			// Array indices have been replace by "replacement TermVariables",
			// here we substitute the replacement TermVariables by a closed form that
			// represents
			// this index in the given iteration `it`
			final Map<TermVariable, Term> closedFormMap = JordanAcceleratedUpdate.constructClosedForm(mgdScript,
					linearUpdate, varMatrixIndexMap, jordanUpdate, it, itHalf, itEven, restrictedVersionPossible);
			final Map<TermVariable, Term> repAssignments = suwr.getIdxRepAssignments();
			final HashMap<Term, Term> substitutionMapping = new HashMap<>();
			for (final TermVariable tv : repAssignments.keySet()) {
				final Term closedFormOfTv = closedFormMap.get(tv);
				assert closedFormOfTv != null;
				substitutionMapping.put(tv, closedFormOfTv);
			}
			closedFormMapWithoutReplacementTvs = closedFormMap.entrySet().stream().collect(Collectors
					.toMap(Map.Entry::getKey, x -> Substitution.apply(mgdScript, substitutionMapping, x.getValue())));
			array2Index2valuesWithoutReplacementTvs = applySubstitutionToIndexAndValue(mgdScript, substitutionMapping,
					suwr.getDeterministicArrayWrites());
		}

		final HashMap<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
			substitutionMapping.put(entry.getKey().getTermVariable(), entry.getValue());
		}
		final HashMap<IProgramVar, Term> closedFormForProgramVar = new HashMap<>();
		for (final IProgramVar pv : suwr.getDeterministicAssignment().keySet()) {
			final Term closedForm1 = closedFormMapWithoutReplacementTvs.get(pv.getTermVariable());
			final Term closedFormForInVars = Substitution.apply(mgdScript, substitutionMapping, closedForm1);
			closedFormForProgramVar.put(pv, closedFormForInVars);
		}
		final NestedMap2<IProgramVar, ArrayIndex, Term> array2Index2values = applySubstitutionToIndexAndValue(mgdScript,
				substitutionMapping, array2Index2valuesWithoutReplacementTvs);
		final ClosedFormOfUpdate closedForm = new ClosedFormOfUpdate(closedFormForProgramVar, array2Index2values);
		return closedForm;
	}

	private static NestedMap2<IProgramVar, ArrayIndex, Term> applySubstitutionToIndexAndValue(final ManagedScript mgdScript,
			final Map<? extends Term, ? extends Term> substitutionMapping,
			final NestedMap2<IProgramVar, ArrayIndex, Term> array2Index2Value) {
		final NestedMap2<IProgramVar, ArrayIndex, Term> result = new NestedMap2<>();
		for (final Triple<IProgramVar, ArrayIndex, Term> triple : array2Index2Value.entrySet()) {
			final List<Term> newIndexEntries = triple.getSecond().stream()
					.map(x -> Substitution.apply(mgdScript, substitutionMapping, x)).collect(Collectors.toList());
			final ArrayIndex newArrayIndex = new ArrayIndex(newIndexEntries);
			final Term newValue = Substitution.apply(mgdScript, substitutionMapping, triple.getThird());
			result.put(triple.getFirst(), newArrayIndex, newValue);
		}
		return result;
	}

	/**
	 * Computes the term guard(closedForm(inVars)).
	 *
	 * @param havocVarReplacements Map that assigns variables that are havoced the term
	 *                         with which they should be replaced.
	 */
	private static Term constructGuardOfClosedForm(final ManagedScript mgdScript,
			final UnmodifiableTransFormula guardTf, final Map<IProgramVar, Term> closedFormOfUpdate,
			final Map<IProgramVar, TermVariable> havocVarReplacements) {
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
	 * @param suwr
	 * @param linearUpdate
	 *
	 * @param isAlternatingClosedFormRequired
	 *            If set we construct a closed from that consists of two formulas one for even iteration steps and one
	 *            for odd iteration steps. Otherwise the is one closed form for all iteration steps.
	 */
	private static UnmodifiableTransFormula createLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final SimultaneousUpdateWithReplacements suwr, final LinearUpdate linearUpdate, final HashMap<Term, Integer> varMatrixIndexMap,
			final JordanTransformationResult jordanUpdate, final UnmodifiableTransFormula loopTransFormula,
			final UnmodifiableTransFormula guardTf, final boolean restrictedVersionPossible,
			final boolean quantifyItFinExplicitly, final boolean isAlternatingClosedFormRequired) {

		final UnmodifiableTransFormula loopAccelerationFormula;
		final Map<IProgramVar, TermVariable> inVars =
				new HashMap<IProgramVar, TermVariable>(loopTransFormula.getInVars());
		final Term xPrimeEqualsX = constructXPrimeEqualsX(mgdScript, inVars, loopTransFormula.getOutVars());
		if (isAlternatingClosedFormRequired) {
			final TermVariable itFinHalf =
					mgdScript.constructFreshTermVariable("itFinHalf", SmtSortUtils.getIntSort(mgdScript.getScript()));
			final Term loopAccelerationTerm = createLoopAccelerationTermAlternating(logger, services, mgdScript, su, suwr,
					linearUpdate, varMatrixIndexMap, jordanUpdate, loopTransFormula, guardTf, quantifyItFinExplicitly,
					itFinHalf, xPrimeEqualsX, inVars);
			loopAccelerationFormula = buildAccelerationFormula(logger, mgdScript, services, loopTransFormula,
					loopAccelerationTerm, quantifyItFinExplicitly, itFinHalf, inVars);
		} else {
			final TermVariable itFin =
					mgdScript.constructFreshTermVariable("itFin", SmtSortUtils.getIntSort(mgdScript.getScript()));
			final Term loopAccelerationTerm = createLoopAccelerationTermSequential(logger, services, mgdScript, su, suwr,
					linearUpdate, varMatrixIndexMap, jordanUpdate, loopTransFormula, guardTf, restrictedVersionPossible,
					quantifyItFinExplicitly, itFin, xPrimeEqualsX, inVars);
			loopAccelerationFormula = buildAccelerationFormula(logger, mgdScript, services, loopTransFormula,
					loopAccelerationTerm, quantifyItFinExplicitly, itFin, inVars);
		}
		assert LoopAccelerationUtils.checkSomePropertiesOfLoopAccelerationFormula(services, mgdScript,
				loopTransFormula, loopAccelerationFormula, REFLEXIVE_TRANSITIVE_CLOSURE);
		return loopAccelerationFormula;
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
	 * @param suwr
	 * @param linearUpdate
	 * @param loopTransFormula
	 * @param guardTf
	 * @return
	 */
	private static Term createLoopAccelerationTermSequential(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final SimultaneousUpdate su,
			final SimultaneousUpdateWithReplacements suwr, final LinearUpdate linearUpdate, final HashMap<Term, Integer> varMatrixIndexMap,
			final JordanTransformationResult jordanUpdate, final UnmodifiableTransFormula loopTransFormula,
			final UnmodifiableTransFormula guardTf, final boolean restrictedVersionPossible,
			final boolean quantifyItFinExplicitly, final TermVariable itFin, final Term xPrimeEqualsX,
			final Map<IProgramVar, TermVariable> inVars) {
		final Script script = mgdScript.getScript();

		final ClosedFormOfUpdate closedFormItFinTuple =
				computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate, varMatrixIndexMap, jordanUpdate, itFin, null,
						loopTransFormula.getInVars(), true, restrictedVersionPossible);
		final Map<IProgramVar, Term> closedFormItFin = closedFormItFinTuple.getScalarUpdates();

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
			final Term leftSideOfImpl = constructIterationRange(script, BigInteger.ONE, it, BigInteger.ONE, itFin);
			final ClosedFormOfUpdate closedFormIt = computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate,
					varMatrixIndexMap, jordanUpdate, it, null, inVars, true, restrictedVersionPossible);
			{
				guardOfClosedFormIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
						guardTf, closedFormIt.getScalarUpdates());
//				conjuncts.add(guardOfClosedFormIt);
////				final Term eq = constructArrayUpdateEquality(script, loopTransFormula.getOutVars(), closedFormIt.getArrayUpdates());
//				final Term rhs = SmtUtils.and(script, guardOfClosedFormIt, guardOfClosedFormIt);
				final Term implication = Util.implies(script, leftSideOfImpl, guardOfClosedFormIt);
				final Set<TermVariable> itSet = new HashSet<>();
				itSet.add(it);
				fourthConjunct = SmtUtils.quantifier(script, 1, itSet, implication);
			}
			conjuncts.add(fourthConjunct);

			final TermVariable idx = mgdScript.constructFreshTermVariable("idx", SmtSortUtils.getIntSort(script));
			// (=> (not (exists ((it Int)) (and (<= 1 it) (<= it (- itFin 1)) (= idx closedForm(it))))) (= a'[idx] a[idx])

			final List<Term> arrayConstraints = new ArrayList<>();
			// a[k] := v
			// a' = (store a k v)
			// ∀idx.       ∀it. (0 <= it < itFin ∧ idx=closedForm_k(it)) ==> a'[idx]=closedForm_v(it)
			//      ∧ (not ∃it. (0 <= it < itFin ∧ idx=closedForm_k(it))) ==> a'[idx]=a[idx]
			for (final Triple<IProgramVar, ArrayIndex, Term> entry : closedFormIt.getArrayUpdates().entrySet()) {
				final ArrayIndex ai = entry.getSecond();
				if (ai.size() > 1) {
					throw new UnsupportedOperationException("multi-dimensional");
				}
//				final TermVariable indexReplacement = (TermVariable) ai.get(0);
//				final Term cf = Substitution.apply(mgdScript, TransFormulaUtils.constructDefaultvarsToInvarsMap(loopTransFormula), suwr.getIdxRepAssignments().get(indexReplacement));

				final Term inRangeIndexEquality;
				{
					final Term cf = ai.get(0);
					final Term eq1 = SmtUtils.equality(script, idx, cf);
					final Term iterationRange = constructIterationRange(script, BigInteger.ONE, it, BigInteger.ZERO, itFin);
					inRangeIndexEquality = SmtUtils.and(script, iterationRange, eq1);
				}
				final Term conjunct1;
				{
					final Term valueUpdate = SmtUtils.equality(script, new MultiDimensionalSelect(loopTransFormula.getOutVars().get(entry.getFirst()), new ArrayIndex(idx), script).toTerm(script), entry.getThird());
					final Term impl1 = SmtUtils.implies(script, inRangeIndexEquality, valueUpdate);
					conjunct1 = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, Collections.singleton(it), impl1);
				}
				final Term conjunct2;
				{
					final Term valueConstancy = SmtUtils.equality(script, new MultiDimensionalSelect(loopTransFormula.getOutVars().get(entry.getFirst()), new ArrayIndex(idx), script).toTerm(script), new MultiDimensionalSelect(loopTransFormula.getInVars().get(entry.getFirst()), new ArrayIndex(idx), script).toTerm(script));
					final Term existsInRangeEquality = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, Collections.singleton(it), inRangeIndexEquality);
					conjunct2 = SmtUtils.implies(script, SmtUtils.not(mgdScript.getScript(), existsInRangeEquality), valueConstancy);
				}
				final Term conjunction = SmtUtils.and(script, conjunct1, conjunct2);
				final Term elim = PartialQuantifierElimination.eliminate(services, mgdScript, conjunction, SimplificationTechnique.SIMPLIFY_DDA);
				final Term all2 = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, Collections.singleton(idx), elim);
				conjuncts.add(all2);
			}
		}
//		conjuncts.add(fourthConjunct);

		// (x' = closedForm(x,itFin))
		final Term xPrimed = constructClosedUpdateConstraint(script, loopTransFormula, su, closedFormItFin);
		conjuncts.add(xPrimed);

		conjuncts.add(guardTf.getFormula());
//		final Term eq = constructArrayUpdateEquality(script, loopTransFormula.getOutVars(),
//				applySubstitutionToIndexAndValue(mgdScript,
//						TransFormulaUtils.constructDefaultvarsToInvarsMap(loopTransFormula),
//						su.getDeterministicArrayWrites()));
//		conjuncts.add(eq);
		final Term transitiveClosure = SmtUtils.and(script, conjuncts);

		final Term accelerationTerm;
		if (REFLEXIVE_TRANSITIVE_CLOSURE) {
			// (and (= itFin 0) (not (guard)) (x'=x))
			final Term reflexiveClosure;
			{
				final Term itFinIs0 = script.term("=", itFin, script.numeral(BigInteger.ZERO));
				if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
					final Term notGuard = Util.not(script, guardTf.getFormula());
					reflexiveClosure = Util.and(script, itFinIs0, notGuard, xPrimeEqualsX);
				} else {
					reflexiveClosure = Util.and(script, itFinIs0, xPrimeEqualsX);
				}
			}
			accelerationTerm = Util.or(script, reflexiveClosure, transitiveClosure);
		} else {
			accelerationTerm = transitiveClosure;
		}

		final Set<TermVariable> itFinSet = new HashSet<>();
		itFinSet.add(itFin);
		final Term quantifiedAccelerationTerm = SmtUtils.quantifier(script, 0, itFinSet, accelerationTerm);

		assert checkPropertiesOfLoopAccelerationFormula(logger, services, mgdScript, loopTransFormula, inVars,
				quantifiedAccelerationTerm, guardTf, xPrimeEqualsX, guardOfClosedFormIt, guardOfClosedFormIt, it, true);

		if (quantifyItFinExplicitly) {
			return quantifiedAccelerationTerm;
		} else {
			return accelerationTerm;
		}
	}

	/**
	 * Construct formula `(and (<= lb it) (<= it (- itFin 1)))`.
	 *
	 * @param lb  The lower bound of the range. The lower bound is itself part of
	 *            the range.
	 * @param ubo The "upper bound offset". A number that is subtracted from the final
	 *            iteration itFin. The difference `ifFin - ubo` is part of the range.
	 */
	private static Term constructIterationRange(final Script script, final BigInteger lb, final TermVariable it,
			final BigInteger ubo, final TermVariable itFin) {
		final Term itGreaterLowerBould = script.term("<=", script.numeral(lb), it);
		final Term itSmallerItFinMinusUbo = script.term("<=", it,
				SmtUtils.minus(script, itFin, script.numeral(ubo)));
		return Util.and(script, itGreaterLowerBould, itSmallerItFinMinusUbo);
	}



	private static Term constructGuardAfterIntermediateIterations(final ManagedScript mgdScript,
			final Set<IProgramVar> havocedVars, final UnmodifiableTransFormula guardTf,
			final Map<IProgramVar, Term> closedFormIt) {
		final Map<IProgramVar, TermVariable> havocReplacements = constructHavocReplacementsForIntermediateIteration(
				mgdScript, havocedVars);
		final Set<TermVariable> havocVarSet = new HashSet<>(havocReplacements.values());
		final Term guardOfClosedFormItUnquantified = constructGuardOfClosedForm(mgdScript, guardTf, closedFormIt,
				havocReplacements);
		return SmtUtils.quantifier(mgdScript.getScript(), QuantifiedFormula.EXISTS, havocVarSet,
				guardOfClosedFormItUnquantified);
	}

	private static Term constructGuardAfterFinalIteration(final ManagedScript mgdScript,
			final Set<IProgramVar> havocedVars, final Map<IProgramVar, TermVariable> outVars,
			final UnmodifiableTransFormula guardTf, final Map<IProgramVar, Term> closedFormItFin) {
		final Map<IProgramVar, TermVariable> havocReplacements = constructHavocReplacementsForFinalIteration(
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
			final SimultaneousUpdate su, final Map<IProgramVar, Term> closedForm) {
		final List<Term> equalities = new ArrayList<>();
		for (final Entry<IProgramVar, Term> entry : su.getDeterministicAssignment().entrySet()) {
			final Term lhs = loopTf.getOutVars().get(entry.getKey());
			final Term rhs = closedForm.get(entry.getKey());
			final Term equality = SmtUtils.binaryEquality(script, lhs, rhs);
			equalities.add(equality);
		}
		return SmtUtils.and(script, equalities);
	}

	@Deprecated
	private static Term constructArrayUpdateEquality(final Script script,
			final Map<IProgramVar, TermVariable> outVars,
			final NestedMap2<IProgramVar, ArrayIndex, Term> arrayUpdates) {
		final List<Term> terms = new ArrayList<>();
		for (final Triple<IProgramVar, ArrayIndex, Term> triple : arrayUpdates.entrySet()) {
			final TermVariable arrayOutVar = outVars.get(triple.getFirst());
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(arrayOutVar, triple.getSecond(), script);
			terms.add(SmtUtils.equality(script, mds.toTerm(script), triple.getThird()));
		}
		return SmtUtils.and(script, terms);
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
	 * @param suwr
	 * @param linearUpdate
	 * @param loopTransFormula
	 * @param guardTf
	 * @return
	 */
	private static Term createLoopAccelerationTermAlternating(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final SimultaneousUpdate su, final SimultaneousUpdateWithReplacements suwr, final LinearUpdate linearUpdate,
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
		final ClosedFormOfUpdate closedFormEvenItFin = computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate,
				varMatrixIndexMap, jordanUpdate, null, itFinHalf, inVars, true, false);
		final Term guardOfClosedFormEvenItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormEvenItFin.getScalarUpdates());

		final ClosedFormOfUpdate closedFormOddItFin = computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate,
				varMatrixIndexMap, jordanUpdate, null, itFinHalf, inVars, false, false);
		final Term guardOfClosedFormOddItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormOddItFin.getScalarUpdates());

		// ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
		final TermVariable itHalf = mgdScript.constructFreshTermVariable("itHalf", sort);
		final Term oneLeqItHalf = script.term("<=", script.numeral(BigInteger.ONE), itHalf);
		final Term itHalfLeqItFinHalfM1 =
				script.term("<=", itHalf, script.term("-", itFinHalf, script.numeral(BigInteger.ONE)));
		final Term forallTerm1Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormEven(x, 2*itHalf)))
		final ClosedFormOfUpdate closedFormEvenIt = computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate,
				varMatrixIndexMap, jordanUpdate, null, itHalf, inVars, true, false);
		final Term guardOfClosedFormEvenIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
				guardTf, closedFormEvenIt.getScalarUpdates());

		// (=> ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term forallTerm1Implication1 = Util.implies(script, forallTerm1Implication1Left, guardOfClosedFormEvenIt);

		// ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1))))
		final Term zeroLeqItHalf = script.term("<=", script.numeral(BigInteger.ZERO), itHalf);
		final Term forallTerm1Implication2Left = Util.and(script, zeroLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormOdd(x, 2*itHalf+1))
		final ClosedFormOfUpdate closedFormOddIt = computeClosedFormOfUpdate(mgdScript, suwr, linearUpdate,
				varMatrixIndexMap, jordanUpdate, null, itHalf, inVars, false, false);
		final Term guardOfClosedFormOddIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
				guardTf, closedFormOddIt.getScalarUpdates());

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
		final Term xPrimedEven = constructClosedUpdateConstraint(script, loopTransFormula, su,
				closedFormEvenItFin.getScalarUpdates());
		// (x' = closedFormOdd(x,2*itFinHalf+1))
		final Term xPrimedOdd = constructClosedUpdateConstraint(script, loopTransFormula, su,
				closedFormOddItFin.getScalarUpdates());

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

		script.echo(new QuotedObject("Check if formula equivalent to false"));
		if (Util.checkSat(script, loopAccelerationTerm) == LBool.UNSAT) {
			logger.warn("Reflexive-transitive closure is equivalent to false");
		}

		final Term notLoopAccFormula = Util.not(script, simplified);
		final Term notGuard = Util.not(script, guardTf.getFormula());
		if (REFLEXIVE_TRANSITIVE_CLOSURE) {
			// Check reflexivity.
			// Check: (x = x') and not (guard(x)) and not (loopAccelerationFormula(x,x')) is unsat.
			// final Term notLoopAccFormula = Util.not(script, loopAccelerationFormula.getFormula());
			if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.UNKNOWN) {
				logger.warn("Unable to prove reflexivity of computed reflexive-transitive closure.");
			}
			if (Util.checkSat(script, Util.and(script, xPrimeEqualsX, notGuard, notLoopAccFormula)) == LBool.SAT) {
				throw new AssertionError("Computed reflexive-transitive closure is not reflexive. Something went wrong"
						+ "in computation of loop acceleration formula.");
			}
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
		final UnmodifiableTransFormula sequentialComposition = TransFormulaUtils.sequentialComposition(logger, services,
				mgdScript, true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				SimplificationTechnique.NONE, loopTransFormulaList);
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

	public static class ClosedFormOfUpdate {
		final Map<IProgramVar, Term> mScalarUpdates;
		final NestedMap2<IProgramVar, ArrayIndex, Term> mArrayUpdates;

		public ClosedFormOfUpdate(final Map<IProgramVar, Term> scalarUpdates,
				final NestedMap2<IProgramVar, ArrayIndex, Term> arrayUpdates) {
			super();
			mScalarUpdates = scalarUpdates;
			mArrayUpdates = arrayUpdates;
		}
		public Map<IProgramVar, Term> getScalarUpdates() {
			return mScalarUpdates;
		}
		public NestedMap2<IProgramVar, ArrayIndex, Term> getArrayUpdates() {
			return mArrayUpdates;
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