/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiIndexArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionDer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Represents a simultaneous variable update that consists of two parts 1.
 * variables that get the value of an term (deterministically assigned) 2.
 * variables that are nondeterministically assigned (havoced)
 *
 * We can often transform {@link TransFormula}s into this form. We note that a
 * {@link TransFormula} is usually not equivalent to this form, because a
 * {@link TransFormula} consists of a guard and an update. The guard can be
 * obtained by {@link TransFormulaUtils#computeGuard}. The conjunction of the
 * guard and the {@link SimultaneousUpdate} (lhs variables considered as outVars
 * all other variables considered as inVars) is equivalent to the original
 * {@link TransFormula}.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class SimultaneousUpdate {

	/**
	 * Reasons why we cannot extract an update of the form `x:=t` from a conjunct.
	 *
	 */
	private enum ExtractionImpediments {
		/**
		 * The conjunct is quantified.
		 */
		QUANTIFIER,
		/**
		 * The conjunct is a disjunction.
		 */
		DISJUNCTION,
		/**
		 * The conjunct is an inequality.
		 */
		INEQUALITY,
		/**
		 * The conjunct is an equality but we cannot find a suitable RHS
		 */
		NORHS,
		/**
		 * A reasons that does not fall in one of the category above.
		 */
		OTHER,
		/**
		 * The conjunct is an array equality but we cannot find a suitable RHS.
		 */
		NORHSARRAY,
	};

	private final Map<IProgramVar, Term> mDeterministicAssignment;
	private final Map<IProgramVar, MultiDimensionalNestedStore> mDeterministicArrayWrites;
	private final Set<IProgramVar> mHavocedVars;
	private final Set<IProgramVar> mReadonlyVars;

	public SimultaneousUpdate(final Map<IProgramVar, Term> deterministicAssignment,
			final Map<IProgramVar, MultiDimensionalNestedStore> deterministicArrayWrites,
			final Set<IProgramVar> havocedVars, final Set<IProgramVar> readonlyVars) {
		super();
		mDeterministicAssignment = deterministicAssignment;
		mDeterministicArrayWrites = deterministicArrayWrites;
		mHavocedVars = havocedVars;
		mReadonlyVars = readonlyVars;
	}

	public static SimultaneousUpdate fromTransFormula(final IUltimateServiceProvider services, final TransFormula tf,
			final ManagedScript mgdScript) throws SimultaneousUpdateException {
		final Set<IProgramVar> havocedVars = new HashSet<>();
		final Set<IProgramVar> assignmentCandidates = new HashSet<>();
		final Set<IProgramVar> unmodifiedVars = new HashSet<>();
		final Set<IProgramVar> allProgVars = TransFormula.collectAllProgramVars(tf);
		for (final IProgramVar pv : allProgVars) {
			if (tf.getInVars().get(pv) == tf.getOutVars().get(pv)) {
				unmodifiedVars.add(pv);
			} else if (tf.isHavocedOut(pv)) {
				havocedVars.add(pv);
			} else {
				assignmentCandidates.add(pv);
			}
		}

		final Map<TermVariable, IProgramVar> inVarsReverseMapping = TransFormulaUtils
				.constructReverseMapping(tf.getInVars());
		final Map<TermVariable, IProgramVar> outVarsReverseMapping = TransFormulaUtils
				.constructReverseMapping(tf.getOutVars());
		final Term[] conjuncts = SmtUtils.getConjuncts(tf.getFormula());
		final HashRelation<IProgramVar, Term> pv2conjuncts = new HashRelation<>();
		for (final Term conjunct : conjuncts) {
			for (final TermVariable tv : conjunct.getFreeVars()) {
				final IProgramVar pv = outVarsReverseMapping.get(tv);
				if (pv != null) {
					pv2conjuncts.addPair(pv, conjunct);
				}
			}
		}
		final Map<IProgramVar, Term> deterministicAssignment = new HashMap<>();
		final Map<IProgramVar, MultiDimensionalNestedStore> deterministicArrayWrites = new HashMap<>();
		for (final IProgramVar pv : assignmentCandidates) {

			final Set<Term> pvContainingConjuncts = pv2conjuncts.getImage(pv);
			if (pvContainingConjuncts.isEmpty()) {
				if (tf.getInVars().get(pv) != tf.getOutVars().get(pv)) {
					throw new AssertionError("in and out have to be similar");
				}
			} else {
				final Term boolConst = isAssignedWithBooleanConstant(mgdScript, tf, pv, pvContainingConjuncts);
				if (boolConst != null) {
					deterministicAssignment.put(pv, boolConst);
				} else {
					// extract
					final TermVariable outVar = tf.getOutVars().get(pv);
					final Pair<Term, Set<ExtractionImpediments>> rhs = extractUpdateRhs(services, outVar, tf,
							inVarsReverseMapping.keySet(), mgdScript);
					assert rhs.getFirst() == null ^ rhs.getSecond() == null;
					if (rhs.getSecond() != null) {
						throw new SimultaneousUpdateException(String.format(
								" Reasons: %s. Size: %s. Cannot find an inVar-based term that is equivalent to %s's outVar %s in TransFormula %s.",
								rhs.getSecond(), new DAGSize().treesize(tf.getFormula()), pv, outVar, tf));
					}
					final Term renamed = rhs.getFirst();
					if (SmtSortUtils.isArraySort(pv.getSort())) {
						if (renamed instanceof TermVariable) {
							deterministicAssignment.put(pv, renamed);
						} else {
							final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.of(renamed);
							if (!pv.getTermVariable().equals(mdns.getArray())) {
								throw new UnsupportedOperationException("Yet, we support only self-updates.");
							}
							deterministicArrayWrites.put(pv, mdns);
						}
					} else {
						deterministicAssignment.put(pv, renamed);
					}
				}
			}
		}

		final Set<IProgramVar> readonlyVariables = new HashSet<>();
		for (final IProgramVar pv : unmodifiedVars) {
			if (isReadInSomeAssignment(pv, deterministicAssignment, deterministicArrayWrites)) {
				readonlyVariables.add(pv);
			}
		}
		return new SimultaneousUpdate(deterministicAssignment, deterministicArrayWrites, havocedVars,
				readonlyVariables);
	}

	private static boolean isReadInSomeAssignment(final IProgramVar pv,
			final Map<IProgramVar, Term> deterministicAssignment,
			final Map<IProgramVar, MultiDimensionalNestedStore> deterministicArrayWrites) {
		for (final Entry<IProgramVar, Term> entry : deterministicAssignment.entrySet()) {
			if (Arrays.asList(entry.getValue().getFreeVars()).contains(pv.getTermVariable())) {
				return true;
			}
		}
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : deterministicArrayWrites.entrySet()) {
			final MultiDimensionalNestedStore mdns = entry.getValue();
			for (final ArrayIndex idx : mdns.getIndices()) {
				if (idx.getFreeVars().contains(pv.getTermVariable())) {
					return true;
				}
			}
			for (final Term value : mdns.getValues()) {
				if (Arrays.asList(value.getFreeVars()).contains(pv.getTermVariable())) {
					return true;
				}
			}
		}
		return false;
	}

	private static Term tryToExtractAssigedTerm(final Script script, final Term conjunction, final TermVariable outVar,
			final Set<TermVariable> outVars) {
		final Term[] conjuncts = SmtUtils.getConjuncts(conjunction);
		for (final Term conjunct : conjuncts) {
			if (Arrays.asList(conjunct.getFreeVars()).contains(outVar)) {
				final PolynomialRelation polyRel = PolynomialRelation.of(script, conjunct);
				final SolvedBinaryRelation sbr = polyRel.solveForSubject(script, outVar);
				if (sbr != null) {
					final Term lhs = sbr.getLeftHandSide();
					if (Arrays.asList(lhs.getFreeVars()).stream().noneMatch(outVars::contains)) {
						return lhs;
					}
				}
			}
		}
		return null;
	}

	private static Term isAssignedWithBooleanConstant(final ManagedScript mgdScript, final TransFormula tf,
			final IProgramVar pv, final Set<Term> pvContainingConjuncts) {
		if (SmtSortUtils.isBoolSort(pv.getTerm().getSort()) && pvContainingConjuncts.size() == 1) {
			final Term conjunct = pvContainingConjuncts.iterator().next();
			if (DualJunctionDer.isSimilarModuloNegation(conjunct, tf.getOutVars().get(pv))) {
				return mgdScript.getScript().term("true");
			}
			if (DualJunctionDer.isDistinctModuloNegation(conjunct, tf.getOutVars().get(pv))) {
				return mgdScript.getScript().term("false");
			}
		}
		return null;
	}


	/**
	 * Given an outVar (which will be the left-hand side of an update in this
	 * application), try to find a term (which will be the right-hand side of an
	 * update in this application) that is equivalent to outVar and whose variables
	 * are inVars. If such a term can be found, rename its inVars to the
	 * corresponding defaultVars and return the renamed term. <br />
	 * TODO: If we see ExtractionImpediments.QUANTIFIER often, we need a different
	 * solution. Otherwise: Refactor and extract methods.
	 */
	private static Pair<Term, Set<ExtractionImpediments>> extractUpdateRhs(final IUltimateServiceProvider services,
			final TermVariable outVar, final TransFormula tf, final Set<TermVariable> inVarSet,
			final ManagedScript mgdScript) {
		// First, project the formula to the outVar and all inVars. E.g., because a
		// suitable equality may be hidden behind a long chain of equalities.
		final Set<TermVariable> nonInvars = Arrays.asList(tf.getFormula().getFreeVars()).stream()
				.filter(x -> x != outVar && !inVarSet.contains(x)).collect(Collectors.toSet());
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), QuantifiedFormula.EXISTS, nonInvars,
				tf.getFormula());
		// Note: A more expensive quantifier elimination would increase the chance to
		// find a result slightly(?) but may be costly.
		final Term eliminated = PartialQuantifierElimination.eliminateLight(services, mgdScript, quantified);
		final Term[] allConjuncts = SmtUtils.getConjuncts(eliminated);
		final Term[] conjunctsWithOutVar = Arrays.stream(allConjuncts)
				.filter(x -> Arrays.asList(x.getFreeVars()).contains(outVar)).toArray(Term[]::new);
		return extractUpdateRhs(outVar, tf, mgdScript, conjunctsWithOutVar);
	}

	public static Pair<Term, Set<ExtractionImpediments>> extractUpdateRhs(final TermVariable outVar,
			final TransFormula tf, final ManagedScript mgdScript, final Term[] conjunctsWithOutVar)
			throws AssertionError {
		final HashSet<ExtractionImpediments> updateImpediments = new HashSet<>();
		for (int i = 0; i < conjunctsWithOutVar.length; i++) {
			final Term conjunct = conjunctsWithOutVar[i];
			if (conjunct instanceof QuantifiedFormula) {
				updateImpediments.add(ExtractionImpediments.QUANTIFIER);
				continue;
			} else if (conjunct instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) conjunct;
				switch (appTerm.getFunction().getName()) {
				case "or": {
					updateImpediments.add(ExtractionImpediments.DISJUNCTION);
					continue;
				}
				case "=":
					final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(appTerm);
					assert ber != null : "Must succeed for equality";
					SolvedBinaryRelation sbr = ber.solveForSubject(mgdScript.getScript(), outVar);
					if (sbr == null) {
						if (SmtSortUtils.isArraySort(outVar.getSort())) {
							final List<ArrayIndex> nondetUpdate = checkForNondeterministicArrayUpdate(outVar, mgdScript,
									conjunctsWithOutVar, i);
							if (nondetUpdate != null) {
								throw new AssertionError("Nondet array update at " + nondetUpdate.size()
								+ " positions with " + (conjunctsWithOutVar.length - 1) + " constraints");
							} else {
								updateImpediments.add(ExtractionImpediments.NORHSARRAY);
								continue;
							}
						}
						// not array sort
						final PolynomialRelation polyRel = PolynomialRelation.of(mgdScript.getScript(), appTerm);
						assert polyRel != null : "Must succeed for equality";
						sbr = polyRel.solveForSubject(mgdScript.getScript(), outVar);
						if (sbr == null) {
							updateImpediments.add(ExtractionImpediments.NORHS);
							continue;
						}
					}
					final Term renamed = TransFormulaUtils.renameInvarsToDefaultVars(tf, mgdScript,
							sbr.getRightHandSide());
					return new Pair<>(renamed, null);
				case "<=":
				case "<":
				case ">=":
				case ">":
					updateImpediments.add(ExtractionImpediments.INEQUALITY);
					continue;
				default:
					updateImpediments.add(ExtractionImpediments.OTHER);
					continue;
				}
			} else {
				throw new UnsupportedOperationException("Unsupported term " + conjunct.getClass().getSimpleName());
			}
		}
		return new Pair<>(null, updateImpediments);
	}

	public static List<ArrayIndex> checkForNondeterministicArrayUpdate(final TermVariable outVar,
			final ManagedScript mgdScript, final Term[] conjunctsWithOutVar, final int k) throws AssertionError {
		assert (SmtSortUtils.isArraySort(outVar.getSort()));
		final MultiIndexArrayUpdate miau = MultiIndexArrayUpdate.of(mgdScript.getScript(), conjunctsWithOutVar[k]);
		if (miau == null) {
			return null;
		}
		if (miau.getNewArray() != outVar) {
			throw new AssertionError("Wrong array");
		}
		if (miau.isNondeterministicUpdate()) {
			int detUpdates = 0;
			int nondetUpdates = 0;
			for (int i = 0; i < miau.getMultiDimensionalNestedStore().getIndices().size(); i++) {
				if (miau.isNondeterministicUpdate(i)) {
					nondetUpdates++;
				} else {
					detUpdates++;
				}
			}
			if (nondetUpdates > 0) {
				final MultiDimensionalNestedStore mdns = miau.getMultiDimensionalNestedStore();
				throw new AssertionError(String.format(
						"Partially nondeterministic update: %s deterministic updates %s nondeterministic updates. Array: %s, Indices: %s, Values: %s",
						detUpdates, nondetUpdates, mdns.getArray(), mdns.getIndices(), mdns.getValues()));
			}
			return null;
		}
		final List<ArrayIndex> indicesOfUpdates = miau.getMultiDimensionalNestedStore().getIndices();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final ArrayIndex ai : indicesOfUpdates) {
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(outVar, ai);
			final TermVariable cellRep = mgdScript.constructFreshTermVariable("tmpCellReplacement", mds.getSort());
			substitutionMapping.put(mds.toTerm(mgdScript.getScript()), cellRep);
		}
		final List<Term> otherConjuncts = DataStructureUtils.copyAllButOne(Arrays.asList(conjunctsWithOutVar), k);
		for (final Term conjunct : otherConjuncts) {
			final Term subst = Substitution.apply(mgdScript, substitutionMapping, conjunct);
			final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(subst.getFreeVars()));
			freeVars.removeAll(substitutionMapping.values());
			if (!freeVars.isEmpty()) {
				throw new AssertionError("Complex constraint for nondet update " + subst);
			}
		}
		return indicesOfUpdates;
	}

	/**
	 * Returns the variables that occur on the right-hand side of updates. Except
	 * for the variables that occur in
	 * {@link SimultaneousUpdate#getDeterministicArrayWrites()}.
	 */
	public Map<IProgramVar, Term> getDeterministicAssignment() {
		return mDeterministicAssignment;
	}


	/**
	 * Returns variables that occur on the right-hand side of an update, where the
	 * update could be identified as a, potentially multi-dimensional, array write.
	 */
	public Map<IProgramVar, MultiDimensionalNestedStore> getDeterministicArrayWrites() {
		return mDeterministicArrayWrites;
	}

	/**
	 * Returns the variables to which a nondeterministic value is assigned.
	 */
	public Set<IProgramVar> getHavocedVars() {
		return mHavocedVars;
	}

	/**
	 * Returns the variables that occur on the left-hand side of updates but never
	 * on the right-hand side.
	 */
	public Set<IProgramVar> getReadonlyVars() {
		return mReadonlyVars;
	}



	/**
	 * Exception that is thrown if we failed to extract a {@link SimultaneousUpdate}
	 * from a {@link TransFormula}. TODO 20210411 This class is work in progress.
	 * Currently we don't know what are the preconditions for a successful
	 * extraction.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 *
	 */
	public static class SimultaneousUpdateException extends Exception {

		public SimultaneousUpdateException(final String errorMessage) {
			super(errorMessage);
		}

	}

}
