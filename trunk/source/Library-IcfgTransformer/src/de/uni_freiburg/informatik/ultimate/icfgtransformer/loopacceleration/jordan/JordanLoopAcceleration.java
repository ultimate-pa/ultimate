/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanDecomposition.JordanDecompositionStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate.NondetArrayWriteConstraints;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate.SimultaneousUpdateException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial.Occurrence;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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

	public static final String UNSUPPORTED_PREFIX = "JordanLoopAcceleration failed";


	/**
	 * Enum that allows us to state which iterations we consider
	 */
	enum Iterations { ALL, EVEN, ODD };

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
			su = SimultaneousUpdate.fromTransFormula(services, loopTransFormula, mgdScript);
		} catch (final SimultaneousUpdateException e) {
			final JordanLoopAccelerationStatisticsGenerator jlasg =
					new JordanLoopAccelerationStatisticsGenerator(-1, -1, -1, -1, new NestedMap2<>(), e.getMessage());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.SIMULTANEOUS_UPDATE_FAILED, e.getMessage(), null,
					jlasg);
		}
		final int numberOfAssignedVariables = su.getDeterministicAssignment().size();
		final int numberOfArrayWrites = su.getDeterministicArrayWrites().size();
		final int numberOfHavocedVariables = su.getHavocedVars().size();

		final Set<Sort> nonIntegerSorts = getNonIntegerSorts(su.getDeterministicAssignment().keySet());
		if (!nonIntegerSorts.isEmpty()) {
			final String errorMessage = "Some updated variables are of non-integer sorts : " + nonIntegerSorts;
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, numberOfArrayWrites, -1, new NestedMap2<>(),
					errorMessage);
			return new JordanLoopAccelerationResult(JordanLoopAccelerationResult.AccelerationStatus.NONINTEGER_UPDATE,
					errorMessage, null, jlasg);
		}

		{
			final Set<TermVariable> tvOfHavoced = su.getHavocedVars().stream().map(IProgramVar::getTermVariable)
					.collect(Collectors.toSet());
			for (final Entry<IProgramVar, Term> entry : su.getDeterministicAssignment().entrySet()) {
				if (!DataStructureUtils.haveEmptyIntersection(
						new HashSet<>(Arrays.asList(entry.getValue().getFreeVars())), tvOfHavoced)) {
					throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Havoced var is read!");
				}
			}
			for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : su.getDeterministicArrayWrites()
					.entrySet()) {
				for (int i = 0; i < entry.getValue().getIndices().size(); i++) {
					if (!DataStructureUtils.haveEmptyIntersection(
							new HashSet<>(entry.getValue().getIndices().get(i).getFreeVars()), tvOfHavoced)) {
						throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Havoced var is read!");
					}

					if (!DataStructureUtils.haveEmptyIntersection(
							new HashSet<>(Arrays.asList(entry.getValue().getValues().get(i).getFreeVars())), tvOfHavoced)) {
						throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Havoced var is read!");
					}
				}
			}
		}

		final Pair<LinearUpdate, String> pair = LinearUpdate.fromSimultaneousUpdate(mgdScript, su);
		if (pair.getFirst() == null) {
			assert pair.getSecond() != null;
			final JordanLoopAccelerationStatisticsGenerator jlasg =
					new JordanLoopAccelerationStatisticsGenerator(numberOfAssignedVariables,
							numberOfHavocedVariables, numberOfArrayWrites, -1, new NestedMap2<>(), pair.getSecond());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.NONLINEAR_UPDATE, pair.getSecond(), null, jlasg);
		}
		final int numberOfReadonlyVariables = pair.getFirst().getReadonlyVariables().size();

		final JordanUpdate jordanUpdate = JordanUpdate.fromLinearUpdate(pair.getFirst());

		if (jordanUpdate.getStatus() == JordanDecompositionStatus.UNSUPPORTED_EIGENVALUES) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, numberOfArrayWrites, numberOfReadonlyVariables,
					new NestedMap2<>(), "Unsupported eigenvalues");
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.UNSUPPORTED_EIGENVALUES, null, null, jlasg);
		}
		assert jordanUpdate.isBlockSizeConsistent(numberOfAssignedVariables, numberOfReadonlyVariables) : "inconsistent blocksize";

		final boolean isAlternatingClosedFormRequired = jordanUpdate.isAlternatingClosedFormRequired();
		final UnmodifiableTransFormula loopAccelerationFormula;
		try {
			loopAccelerationFormula = createLoopAccelerationFormula(logger, services,
					mgdScript, su, pair.getFirst(), jordanUpdate, loopTransFormula, quantifyItFinExplicitly,
					isAlternatingClosedFormRequired);
		} catch (final UnsupportedOperationException uoe) {
			final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
					numberOfAssignedVariables, numberOfHavocedVariables, numberOfArrayWrites, numberOfReadonlyVariables,
					jordanUpdate.getJordanBlockSizes(), uoe.getMessage());
			return new JordanLoopAccelerationResult(
					JordanLoopAccelerationResult.AccelerationStatus.OTHER, null, null, jlasg);
		}
		final JordanLoopAccelerationStatisticsGenerator jlasg = new JordanLoopAccelerationStatisticsGenerator(
				numberOfAssignedVariables, numberOfHavocedVariables, numberOfArrayWrites, numberOfReadonlyVariables,
				jordanUpdate.getJordanBlockSizes(), "");
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
	 * Compute the closed form given the update. Variables of the
	 * {@link TransFormula} that occur in the update are represented by their
	 * inVars.
	 */
	private static ClosedFormOfUpdate computeClosedFormOfUpdate(final ManagedScript mgdScript,
			final SimultaneousUpdate su, final TermVariable it,
			final Map<IProgramVar, TermVariable> inVars, final Map<TermVariable, Term> closedFormMap) {
		// TODO 20220914 Matthias: Maybe this is not the right place for this check. The
		// check is yet too strict,
		// we support at least array writes where indices contain arrays that are not
		// modified.
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : su.getDeterministicArrayWrites().entrySet()) {
			for (int i = 0; i < entry.getValue().getIndices().size(); i++) {
				final ArrayIndex idx = entry.getValue().getIndices().get(i);
				for (final TermVariable tv : idx.getFreeVars()) {
					if (SmtSortUtils.isArraySort(tv.getSort())) {
						throw new UnsupportedOperationException("ArrayIndex contains some array variable");
					}
				}
				if (su.getNondetArrayWriteConstraints().get(entry.getKey()).isNondeterministicArrayUpdate(i)) {
					continue;
				}
				final Term value = entry.getValue().getValues().get(i);
				final Collection<ArrayStore> stores = ArrayStore.extractStores(value, true);
				if (!stores.isEmpty()) {
					throw new UnsupportedOperationException("Value contains some stores");
				}

				final List<MultiDimensionalSelect> selects = MultiDimensionalSelect.extractSelectDeep(value);
				if (selects.size() > 1) {
					// FIXME 20230606 Matthias: Occurs sedomly, do not support by now
					throw new UnsupportedOperationException(
							String.format("Written value contains %s selects: %s", selects.size(), selects));
				}
				if (selects.size() == 1) {
					final MultiDimensionalSelect mds = selects.get(0);
					if (entry.getValue().getArray() == mds.getArray()) {
						throw new UnsupportedOperationException(String.format(
								"Array update for index %s writes a value that reads the same array at index %s", idx,
								mds.getIndex()));
					} else {
						throw new UnsupportedOperationException(
								String.format("Update of array %s with value that reads from array %s",
										entry.getValue().getArray(), mds.getArray()));
					}
				}
				for (final TermVariable tv : Arrays.asList(value.getFreeVars())) {
					if (SmtSortUtils.isArraySort(tv.getSort())) {
						throw new UnsupportedOperationException("Written value contains modified array variable");
					}
				}
			}
		}
		// Map that assigns to the default TermVariable of an IProgramVar its closed
		// form, where each variable in the closed form is represented by its inVar.
		final Map<TermVariable, Term> closedFormWithInvarsMap;
		{
			closedFormWithInvarsMap = new HashMap<>();
			final HashMap<Term, Term> defaultTv2inVar = new HashMap<>();
			for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
				defaultTv2inVar.put(entry.getKey().getTermVariable(), entry.getValue());
			}
			for (final Entry<TermVariable, Term> entry : closedFormMap.entrySet()) {
				closedFormWithInvarsMap.put(entry.getKey(),
						Substitution.apply(mgdScript, defaultTv2inVar, entry.getValue()));
			}
		}
		final HashMap<IProgramVar, Term> closedFormForProgramVar = new HashMap<>();
		for (final IProgramVar pv : su.getDeterministicAssignment().keySet()) {
			closedFormForProgramVar.put(pv, closedFormWithInvarsMap.get(pv.getTermVariable()));
		}
		// Mapping in which that maps default TermVariables to their closed form (where
		// variables are represented by inVars). Since array indices may also contain
		// read-only variables we have to add from the inVars mapping.
		final HashMap<TermVariable, Term> substitutionMapping = new HashMap<>(closedFormWithInvarsMap);
		for (final IProgramVar pv : su.getReadonlyVars()) {
			final Term oldValue = substitutionMapping.put(pv.getTermVariable(), inVars.get(pv));
			if (oldValue != null) {
				throw new AssertionError(String.format("Contradiction: %s is readonly and modified", pv));
			}
		}
		final Map<IProgramVar, MultiDimensionalNestedStore> arrayWrites = applySubstitutionToIndexAndValue(mgdScript,
				substitutionMapping, su.getDeterministicArrayWrites());
		final ClosedFormOfUpdate res = new ClosedFormOfUpdate(closedFormForProgramVar, arrayWrites, su.getNondetArrayWriteConstraints());
		checkIndices(mgdScript, arrayWrites, it);
		return res;
	}

	private static void checkIndices(final ManagedScript mgdScript,
			final Map<IProgramVar, MultiDimensionalNestedStore> array2Index2values, final TermVariable it) {
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : array2Index2values.entrySet()) {
			final MultiDimensionalNestedStore mdns = entry.getValue();
			for (int i = 0; i < mdns.getIndices().size(); i++) {
				checkIndex(mgdScript, mdns.getIndices().get(i), it);
			}
		}
	}

	private static void checkIndex(final ManagedScript mgdScript, final ArrayIndex index, final TermVariable it) {
		final List<IPolynomialTerm> polyIndex = index.stream()
				.map(x -> PolynomialTermTransformer.convert(mgdScript.getScript(), x)).collect(Collectors.toList());
		if (isStrictlyMonotone(polyIndex, it)) {
			return;
		} else {
			throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Index not moving: " + index);
		}
	}

	private static boolean isStrictlyMonotone(final List<IPolynomialTerm> polyIndex, final TermVariable it) {
		boolean strictlyMonotone = false;
		for (final IPolynomialTerm poly : polyIndex) {
			for (final Entry<Monomial, Rational> entry : poly.getMonomial2Coefficient().entrySet()) {
				final Occurrence occ = entry.getKey().isExclusiveVariable(it);
				if (occ == Occurrence.NON_EXCLUSIVE_OR_SUBTERM) {
					throw new UnsupportedOperationException(
							UNSUPPORTED_PREFIX + " Probably not monotone: " + entry.getKey());
				} else if (occ == Occurrence.AS_EXCLUSIVE_VARIABlE) {
					strictlyMonotone = true;
				}
			}
		}
		return strictlyMonotone;
	}


	private static Map<IProgramVar, MultiDimensionalNestedStore> applySubstitutionToIndexAndValue(
			final ManagedScript mgdScript, final Map<? extends Term, ? extends Term> substitutionMapping,
			final Map<IProgramVar, MultiDimensionalNestedStore> map) {
		final Map<IProgramVar, MultiDimensionalNestedStore> result = new HashMap<>();
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : map.entrySet()) {
			result.put(entry.getKey(), entry.getValue().applySubstitution(mgdScript, substitutionMapping));
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
	 * @param isAlternatingClosedFormRequired
	 *            If set we construct a closed from that consists of two formulas one for even iteration steps and one
	 *            for odd iteration steps. Otherwise the is one closed form for all iteration steps.
	 */
	private static UnmodifiableTransFormula createLoopAccelerationFormula(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final SimultaneousUpdate su,
			final LinearUpdate linearUpdate, final JordanUpdate jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final boolean quantifyItFinExplicitly,
			final boolean isAlternatingClosedFormRequired) {

		final int sizeOfLargestEv0Block = jordanUpdate.computeSizeOfLargestEv0Block();
		assert sizeOfLargestEv0Block >= 0;

		final UnmodifiableTransFormula guardTf = TransFormulaUtils.computeGuard(loopTransFormula, mgdScript, services);
		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(loopTransFormula.getInVars());
		// The call of `constructXPrimeEqualsX` might add entries to the newInVars.
		final Term xPrimeEqualsX = constructXPrimeEqualsX(mgdScript, newInVars, loopTransFormula.getOutVars());

		final List<Term> disjuncts = new ArrayList<>();
		if (sizeOfLargestEv0Block > 1) {
			// we have to consider the first sizeOfLargestEv0Block-1 iterations separately
			for (int i = 1; i < sizeOfLargestEv0Block; i++) {
				final List<Term> guards = new ArrayList<>();
				for (int j = 1; j <= i; j++) {
					final Term guard = constructGuardForFixedIteration(mgdScript, su.getHavocedVars(), guardTf, j,
							jordanUpdate, su, newInVars);
					guards.add(guard);
				}
				final Term guard = SmtUtils.and(mgdScript.getScript(), guards);
				final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, i);
				final ClosedFormOfUpdate closedFormForI = computeClosedFormOfUpdate(mgdScript, su, null, newInVars,
						closedFormMap);
				final Term update = constructClosedUpdateConstraint(mgdScript.getScript(), loopTransFormula, su,
						closedFormForI.getScalarUpdates());
				if (!closedFormForI.getArrayUpdates().isEmpty()) {
					throw new UnsupportedOperationException(
							String.format(UNSUPPORTED_PREFIX + " Consider first %s iterations separately for arrays",
									sizeOfLargestEv0Block));
				}
				final Term disjunct = SmtUtils.and(mgdScript.getScript(), guard, update);
				disjuncts.add(disjunct);
			}

		}

		final Term transitiveClosure;
		final TermVariable itFin;
		if (isAlternatingClosedFormRequired) {
			if (!su.getDeterministicArrayWrites().isEmpty()) {
				throw new UnsupportedOperationException(
						UNSUPPORTED_PREFIX + " If alternating form is required we do not yet support arrays");
			}
			if (sizeOfLargestEv0Block > 1) {
				throw new UnsupportedOperationException(String.format(UNSUPPORTED_PREFIX
						+ " If alternating form is required we cannot yet consider first %s iterations separately",
						sizeOfLargestEv0Block));
			}
			itFin = mgdScript.constructFreshTermVariable("itFinHalf", SmtSortUtils.getIntSort(mgdScript.getScript()));
			transitiveClosure = createLoopAccelerationTermAlternating(logger, services, mgdScript, su, linearUpdate,
					jordanUpdate, loopTransFormula, guardTf, itFin, newInVars);
		} else {
			itFin = mgdScript.constructFreshTermVariable("itFin", SmtSortUtils.getIntSort(mgdScript.getScript()));
			final int firstIteration = Math.max(sizeOfLargestEv0Block, 1);
			transitiveClosure = createLoopAccelerationTermSequential(services, mgdScript, su, jordanUpdate,
					loopTransFormula, guardTf, itFin, newInVars, firstIteration);
		}
		disjuncts.add(transitiveClosure);
		if (REFLEXIVE_TRANSITIVE_CLOSURE) {
			// (and (not (guard)) (x'=x))
			final Term reflexiveClosure;
			{
				if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
					final Term notGuard = Util.not(mgdScript.getScript(), guardTf.getFormula());
					reflexiveClosure = Util.and(mgdScript.getScript(), notGuard, xPrimeEqualsX);
				} else {
					reflexiveClosure = Util.and(mgdScript.getScript(), xPrimeEqualsX);
				}
			}
			disjuncts.add(reflexiveClosure);
		}
		final Term accelerationTerm = SmtUtils.or(mgdScript.getScript(), disjuncts);
		final UnmodifiableTransFormula loopAccelerationFormula = buildAccelerationTransFormula(logger, mgdScript,
				services, loopTransFormula, accelerationTerm, quantifyItFinExplicitly, itFin, newInVars);

		assert LoopAccelerationUtils.checkSomePropertiesOfLoopAccelerationFormula(services, mgdScript, loopTransFormula,
				loopAccelerationFormula, REFLEXIVE_TRANSITIVE_CLOSURE);
		return loopAccelerationFormula;
	}

	/**
	 * Simplify the term representing the loop acceleration formula and build UnmodifiableTransFormula.
	 */
	private static UnmodifiableTransFormula buildAccelerationTransFormula(final ILogger logger,
			final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final UnmodifiableTransFormula loopTransFormula, final Term loopAccelerationTerm,
			final boolean quantifyItFinExplicitly, final TermVariable itFin,
			final Map<IProgramVar, TermVariable> inVars) {
		final Term nnf =
				new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(loopAccelerationTerm);
		final Term loopAccelerationFormulaWithoutQuantifiers = PartialQuantifierElimination.eliminateCompat(services,
				mgdScript, true, PqeTechniques.ALL, SimplificationTechnique.NONE, nnf);
		// TODO 20220724 Matthias: Simplification after quantifier elimination is typically superfluous.
		final Term simplified = SmtUtils.simplify(mgdScript, loopAccelerationFormulaWithoutQuantifiers,
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA2);

		UnmodifiableTransFormula loopAccelerationFormula;
		if (quantifyItFinExplicitly) {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, loopTransFormula.getOutVars(),
					loopTransFormula.getNonTheoryConsts().isEmpty(), loopTransFormula.getNonTheoryConsts(),
					loopTransFormula.getBranchEncoders().isEmpty(), loopTransFormula.getBranchEncoders(),
					loopTransFormula.getAuxVars().isEmpty());
			tfb.setInfeasibility(loopTransFormula.isInfeasible());
			Term quantified = SmtUtils.quantifier(mgdScript.getScript(), QuantifiedFormula.EXISTS,
					Collections.singleton(itFin), simplified);
			quantified = PartialQuantifierElimination.eliminateCompat(services,
					mgdScript, true, PqeTechniques.ALL, SimplificationTechnique.SIMPLIFY_DDA2, quantified);
			tfb.setFormula(quantified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);
		} else {
			final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, loopTransFormula.getOutVars(),
					loopTransFormula.getNonTheoryConsts().isEmpty(), loopTransFormula.getNonTheoryConsts(),
					loopTransFormula.getBranchEncoders().isEmpty(), loopTransFormula.getBranchEncoders(), false);
			tfb.addAuxVar(itFin);
			tfb.setInfeasibility(loopTransFormula.isInfeasible());
			tfb.setFormula(simplified);
			loopAccelerationFormula = tfb.finishConstruction(mgdScript);
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
	 * @param firstIteration
	 */
	private static Term createLoopAccelerationTermSequential(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final SimultaneousUpdate su, final JordanUpdate jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final TermVariable itFin, final Map<IProgramVar, TermVariable> inVars, final int firstIteration) {
		if (firstIteration < 1) {
			throw new IllegalArgumentException("Cannot construct constraint for non-positive iterations");
		}
		final Script script = mgdScript.getScript();

		final ClosedFormOfUpdate closedFormItFinTuple;
		{
			final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, itFin, null,
					Iterations.ALL);
			closedFormItFinTuple = computeClosedFormOfUpdate(mgdScript, su, itFin, loopTransFormula.getInVars(),
					closedFormMap);
		}
		final Map<IProgramVar, Term> closedFormItFin = closedFormItFinTuple.getScalarUpdates();

		final List<Term> conjuncts = new ArrayList<>();
		for (int i = 1; i < firstIteration; i++) {
			// Construct guards for all iterations before our first iteration
			final Term guard = constructGuardForFixedIteration(mgdScript, su.getHavocedVars(), guardTf, i, jordanUpdate,
					su, inVars);
			conjuncts.add(guard);
		}
		// We have to handle the guard of our first iteration separately, because this
		// guard utilizes the closed form from the preceding iteration.
		conjuncts.add(constructGuardForFixedIteration(mgdScript, su.getHavocedVars(), guardTf, firstIteration,
				jordanUpdate, su, inVars));

		if (CONCATENATE_WITH_NEGATION_OF_GUARD) {
			// Construct subformula guard(cf(x,itFin)).
			final Term guardOfClosedFormItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
					loopTransFormula.getOutVars(), guardTf, closedFormItFin);
			// (not (guard(closedForm(x, itFin))))
			final Term notGuardOfCf = Util.not(script, guardOfClosedFormItFin);
			conjuncts.add(notGuardOfCf);
		}

		// We presume the final iteration is at least our first iteration.
		// (>= itFin firstIteration)
		final Term firstConjunct = script.term(">=", itFin, script.numeral(BigInteger.valueOf(firstIteration)));
		conjuncts.add(firstConjunct);

		// (forall ((it Int)) (=> (and (<= 1 it) (<= it (- itFin 1)))
		// (guard(closedForm(x,it)))))
		final TermVariable it = mgdScript.constructFreshTermVariable("it", SmtSortUtils.getIntSort(script));
		final Term fourthConjunct;
		final Term guardOfClosedFormIt;
		{
			final Term leftSideOfImpl = constructIterationRange(script, BigInteger.valueOf(firstIteration), it,
					BigInteger.ONE, itFin);
			final ClosedFormOfUpdate closedFormIt;
			{
				final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, it, null,
						Iterations.ALL);
				closedFormIt = computeClosedFormOfUpdate(mgdScript, su, it, inVars, closedFormMap);
			}
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

			final List<Term> arrayConstraints = constructArrayUpdateConstraints(services, mgdScript, loopTransFormula,
					itFin, it, closedFormIt);
			conjuncts.addAll(arrayConstraints);
		}
//		conjuncts.add(fourthConjunct);

		// (x' = closedForm(x,itFin))
		final Term xPrimed = constructClosedUpdateConstraint(script, loopTransFormula, su, closedFormItFin);
		conjuncts.add(xPrimed);


//		final Term eq = constructArrayUpdateEquality(script, loopTransFormula.getOutVars(),
//				applySubstitutionToIndexAndValue(mgdScript,
//						TransFormulaUtils.constructDefaultvarsToInvarsMap(loopTransFormula),
//						su.getDeterministicArrayWrites()));
//		conjuncts.add(eq);
		final Term transitiveClosure = SmtUtils.and(script, conjuncts);
		return transitiveClosure;
	}

	private static List<Term> constructArrayUpdateConstraints(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final UnmodifiableTransFormula loopTransFormula, final TermVariable itFin,
			final TermVariable it, final ClosedFormOfUpdate closedFormIt) {
		final Script script = mgdScript.getScript();

		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : closedFormIt.getArrayUpdates().entrySet()) {
			final IProgramVar array = entry.getKey();
			final MultiDimensionalNestedStore mdns = entry.getValue();
			if (mdns.getIndices().size() > 1) {
				final StringBuilder sb = new StringBuilder();
				int indexPairs = 0;
				int movingInLockstep = 0;
				final List<ArrayIndex> indices = mdns.getIndices();
				for (int i = 0; i < indices.size(); i++) {
					for (int j = i + 1; j < indices.size(); j++) {
						indexPairs++;
						final ArrayIndex diff = indices.get(i).minus(script, indices.get(j));
						sb.append(diff);
						sb.append(" ");
						if (diff.getFreeVars().isEmpty()) {
							movingInLockstep++;
						}
					}
				}
				throw new UnsupportedOperationException(
						String.format("%s updates on array %s. %s indexPairs, %s moving in lockstep. Differences: %s",
								indices.size(), array, indexPairs, movingInLockstep, sb.toString()));
			}
		}

		final List<Term> arrayUpdateConstraints = new ArrayList<>();
		// a[k] := v
		// a' = (store a k v)
		// ∀idx. ∀it. (0 <= it < itFin ∧ idx=closedForm_k(it)) ==> a'[idx]=closedForm_v(it)
		//          ∧ (not ∃it. (0 <= it < itFin ∧ idx=closedForm_k(it))) ==> a'[idx]=a[idx]
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : closedFormIt.getArrayUpdates().entrySet()) {
			final IProgramVar array = entry.getKey();
			final MultiDimensionalNestedStore mdns = entry.getValue();
			if (mdns.getIndices().size() > 1) {
				throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Several updates per array");
			}
			final ArrayIndex index = mdns.getIndices().get(0);
			final List<TermVariable> idx = constructIdxTermVariables(mgdScript, index.size());
			final Term inRangeIndexEquality;
			{
				final Term eq1 = SmtUtils.pairwiseEquality(script, idx, index);
				final Term iterationRange = constructIterationRange(script, BigInteger.ZERO, it, BigInteger.ONE, itFin);
				inRangeIndexEquality = SmtUtils.and(script, iterationRange, eq1);
			}
			final List<Term> constraints = new ArrayList<>();
			{
				final Term valueConstraint;
				final Term arrayCell = new MultiDimensionalSelect(loopTransFormula.getOutVars().get(array),
						new ArrayIndex(idx)).toTerm(script);
				if (!closedFormIt.getNondetArrayWriteConstraints().get(array).isNondeterministicArrayUpdate(0)) {
					// deterministic update: we give the array cell a new value
					final Term value = mdns.getValues().get(0);
					final Term valueUpdate = SmtUtils.equality(script, arrayCell, value);
					valueConstraint = valueUpdate;
				} else {
					// nondeterministic update: we add some constraints for the value of the cell.
					// If there are no constraints, we use `true` and the `inRangeConstraint`
					// (below) will also become true
					valueConstraint = closedFormIt.getNondetArrayWriteConstraints().get(array)
							.constructConstraints(script, 0, arrayCell);
				}
				final Term impl1 = SmtUtils.implies(script, inRangeIndexEquality, valueConstraint);
				final Term quantified = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, Collections.singleton(it),
						impl1);
				final Term inRangeConstraint = PartialQuantifierElimination.eliminate(services, mgdScript, quantified,
						SimplificationTechnique.SIMPLIFY_DDA2);
				constraints.add(inRangeConstraint);
			}
			{
				final Term valueConstancy = SmtUtils.equality(script,
						new MultiDimensionalSelect(loopTransFormula.getOutVars().get(array), new ArrayIndex(idx))
								.toTerm(script),
						new MultiDimensionalSelect(loopTransFormula.getInVars().get(array), new ArrayIndex(idx))
								.toTerm(script));
				final Term existsInRangeEquality = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS,
						Collections.singleton(it), inRangeIndexEquality);
				final Term quantified = SmtUtils.implies(script,
						SmtUtils.not(mgdScript.getScript(), existsInRangeEquality), valueConstancy);
				final Term outsideRangeConstraint = PartialQuantifierElimination.eliminate(services, mgdScript,
						quantified, SimplificationTechnique.SIMPLIFY_DDA2);
				constraints.add(outsideRangeConstraint);
			}
			final Term conjunction = SmtUtils.and(script, constraints);
			// No need to apply quantifier elimination to conjunction, each conjunct
			// addresses a different range hence no conjunct can simplify the other.
			final Term all2 = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, idx, conjunction);
			arrayUpdateConstraints.add(all2);
		}
		return arrayUpdateConstraints;
	}

	private static List<TermVariable> constructIdxTermVariables(final ManagedScript mgdScript, final int dimension) {
		assert dimension >= 1;
		final Sort intSort = SmtSortUtils.getIntSort(mgdScript.getScript());
		if (dimension == 1) {
			return Collections.singletonList(mgdScript.constructFreshTermVariable("idx", intSort));
		} else if (dimension == 2) {
			return Arrays.asList(new TermVariable[] { mgdScript.constructFreshTermVariable("idxDim1", intSort),
					mgdScript.constructFreshTermVariable("idxDim2", intSort) });
		} else {
			// TODO: Works analogously to two dimensions, but I did not had examples to test
			// an implementation.
			throw new UnsupportedOperationException(UNSUPPORTED_PREFIX + " Dimension not yet supported: " + dimension);
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

	private static Term constructGuardForFixedIteration(final ManagedScript mgdScript,
			final Set<IProgramVar> havocedVars, final UnmodifiableTransFormula guardTf, final int k,
			final JordanUpdate jordanUpdate, final SimultaneousUpdate su,
			final Map<IProgramVar, TermVariable> inVars) {
		if (k < 1) {
			throw new IllegalArgumentException();
		}
		if (k == 1) {
			return guardTf.getFormula();
		}
		final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, k-1);
		final ClosedFormOfUpdate closedFormForK = computeClosedFormOfUpdate(mgdScript, su, null, inVars, closedFormMap);
		return constructGuardAfterIntermediateIterations(mgdScript, havocedVars, guardTf,
				closedFormForK.getScalarUpdates());
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
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(arrayOutVar, triple.getSecond());
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
	 */
	private static Term createLoopAccelerationTermAlternating(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final SimultaneousUpdate su, final LinearUpdate linearUpdate,
			final JordanUpdate jordanUpdate,
			final UnmodifiableTransFormula loopTransFormula, final UnmodifiableTransFormula guardTf,
			final TermVariable itFinHalf, final Map<IProgramVar, TermVariable> inVars) {

		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);

		// (> itFinHalf 0)
		final Term itFinHalfGreater0 = script.term(">", itFinHalf, script.numeral(BigInteger.ZERO));

		// (not (guard(closedFormEven(x, 2*itFinHalf))))
		final ClosedFormOfUpdate closedFormEvenItFin;
		{
			final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript,
					null, itFinHalf, Iterations.EVEN);
			closedFormEvenItFin = computeClosedFormOfUpdate(mgdScript, su, null,
					inVars, closedFormMap);
		}
		final Term guardOfClosedFormEvenItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormEvenItFin.getScalarUpdates());

		final ClosedFormOfUpdate closedFormOddItFin;
		{
			final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, null, itFinHalf,
					Iterations.ODD);
			closedFormOddItFin = computeClosedFormOfUpdate(mgdScript, su, null, inVars, closedFormMap);
		}
		final Term guardOfClosedFormOddItFin = constructGuardAfterFinalIteration(mgdScript, su.getHavocedVars(),
				loopTransFormula.getOutVars(), guardTf, closedFormOddItFin.getScalarUpdates());

		// ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1)))
		final TermVariable itHalf = mgdScript.constructFreshTermVariable("itHalf", sort);
		final Term oneLeqItHalf = script.term("<=", script.numeral(BigInteger.ONE), itHalf);
		final Term itHalfLeqItFinHalfM1 =
				script.term("<=", itHalf, script.term("-", itFinHalf, script.numeral(BigInteger.ONE)));
		final Term forallTerm1Implication1Left = Util.and(script, oneLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormEven(x, 2*itHalf)))
		final ClosedFormOfUpdate closedFormEvenIt;
		{
			final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, null, itHalf,
					Iterations.EVEN);
			closedFormEvenIt = computeClosedFormOfUpdate(mgdScript, su, null,
				inVars, closedFormMap);
		}
		final Term guardOfClosedFormEvenIt = constructGuardAfterIntermediateIterations(mgdScript, su.getHavocedVars(),
				guardTf, closedFormEvenIt.getScalarUpdates());

		// (=> ((and (<= 1 itHalf) (<= itHalf (- itFinHalf 1))) (guard(closedFormEven(x,
		// 2*itHalf))))
		final Term forallTerm1Implication1 = Util.implies(script, forallTerm1Implication1Left, guardOfClosedFormEvenIt);

		// ((and (<= 0 itHalf) (<= itHalf (- itFinHalf 1))))
		final Term zeroLeqItHalf = script.term("<=", script.numeral(BigInteger.ZERO), itHalf);
		final Term forallTerm1Implication2Left = Util.and(script, zeroLeqItHalf, itHalfLeqItFinHalfM1);

		// (guard(closedFormOdd(x, 2*itHalf+1))
		final ClosedFormOfUpdate closedFormOddIt;
		{
			final Map<TermVariable, Term> closedFormMap = jordanUpdate.constructClosedForm(mgdScript, null, itHalf,
					Iterations.ODD);
			closedFormOddIt = computeClosedFormOfUpdate(mgdScript, su, null,
				inVars, closedFormMap);
		}
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
		final Term disjunction = Util.or(script, innerConjunction1, innerConjunction2);
		return disjunction;
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
				mgdScript.term(null, "true"), services, SimplificationTechnique.SIMPLIFY_DDA2);

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
		final Term notGuardOfClosedForm2 = Util.not(script,
				PureSubstitution.apply(script, substitutionMapping2, guardOfClosedFormEven));

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
		private final Map<IProgramVar, Term> mScalarUpdates;
		private final Map<IProgramVar, MultiDimensionalNestedStore> mArrayUpdates;
		private final Map<IProgramVar, NondetArrayWriteConstraints> mNondetArrayWriteConstraints;

		public ClosedFormOfUpdate(final Map<IProgramVar, Term> scalarUpdates,
				final Map<IProgramVar, MultiDimensionalNestedStore> arrayUpdates,
				final Map<IProgramVar, NondetArrayWriteConstraints> nondetArrayWriteConstraints) {
			super();
			mScalarUpdates = scalarUpdates;
			mArrayUpdates = arrayUpdates;
			mNondetArrayWriteConstraints = nondetArrayWriteConstraints;
		}
		public Map<IProgramVar, Term> getScalarUpdates() {
			return mScalarUpdates;
		}
		public Map<IProgramVar, MultiDimensionalNestedStore> getArrayUpdates() {
			return mArrayUpdates;
		}
		public Map<IProgramVar, NondetArrayWriteConstraints> getNondetArrayWriteConstraints() {
			return mNondetArrayWriteConstraints;
		}

	}

	public static class JordanLoopAccelerationResult {
		public enum AccelerationStatus {
			SUCCESS, SIMULTANEOUS_UPDATE_FAILED, NONINTEGER_UPDATE, NONLINEAR_UPDATE, UNSUPPORTED_EIGENVALUES, OTHER,
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