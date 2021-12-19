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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionDer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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

	private final Map<IProgramVar, Term> mDeterministicAssignment;
	private final Set<IProgramVar> mHavocedVars;
	private final Set<IProgramVar> mReadonlyVars;

	public SimultaneousUpdate(final Map<IProgramVar, Term> deterministicAssignment,
			final Set<IProgramVar> havocedVars, final Set<IProgramVar> readonlyVars) {
		super();
		mDeterministicAssignment = deterministicAssignment;
		mHavocedVars = havocedVars;
		mReadonlyVars = readonlyVars;
	}

	public static SimultaneousUpdate fromTransFormula(final TransFormula tf, final ManagedScript mgdScript)
			throws SimultaneousUpdateException {
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
					final Term pvContainingConjunct = pvContainingConjuncts.iterator().next();
					final Term forbiddenTerm = null;
					final TermVariable outVar = tf.getOutVars().get(pv);
					final Term renamed = extractUpdateRhs(outVar, conjuncts, forbiddenTerm, inVarsReverseMapping,
							outVarsReverseMapping, mgdScript);
					if (renamed == null) {
						throw new SimultaneousUpdateException("cannot bring into simultaneous update form " + pv
								+ "'s outvar occurs in several conjuncts " + Arrays.toString(conjuncts));
					}
					deterministicAssignment.put(pv, renamed);
				}
			}
		}

		final Set<IProgramVar> readonlyVariables = new HashSet<>();
		for (final IProgramVar pv : unmodifiedVars) {
			if (isReadInSomeAssignment(pv, deterministicAssignment)) {
				readonlyVariables.add(pv);
			}
		}
		return new SimultaneousUpdate(deterministicAssignment, havocedVars, readonlyVariables);
	}

	private static boolean isReadInSomeAssignment(final IProgramVar pv,
			final Map<IProgramVar, Term> deterministicAssignment) {
		for (final Entry<IProgramVar, Term> entry : deterministicAssignment.entrySet()) {
			if (Arrays.asList(entry.getValue().getFreeVars()).contains(pv.getTermVariable())) {
				return true;
			}
		}
		return false;
	}

	private static Term tryToExtractAssigedTerm(final Script script, final Term conjunction, final TermVariable outVar,
			final Set<TermVariable> outVars) {
		final Term[] conjuncts = SmtUtils.getConjuncts(conjunction);
		for (final Term conjunct : conjuncts) {
			if (Arrays.asList(conjunct.getFreeVars()).contains(outVar)) {
				final PolynomialRelation polyRel = PolynomialRelation.convert(script, conjunct);
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

	private static Term extractUpdateRhs(final TermVariable outVar, final Term[] conjuncts, final Term forbiddenTerm,
			final Map<TermVariable, IProgramVar> inVarsReverseMapping,
			final Map<TermVariable, IProgramVar> outVarsReverseMapping, final ManagedScript mgdScript)
			throws SimultaneousUpdateException {
		final EqualityInformation ei = EqualityInformation.getEqinfo(mgdScript.getScript(), outVar, conjuncts,
				forbiddenTerm, QuantifiedFormula.EXISTS);
		if (ei == null) {
			return null;
		}
		final Term rhs = ei.getRelatedTerm();
		final Map<Term, Term> substitutionMapping = computeSubstitutionMapping(rhs, conjuncts, outVar,
				inVarsReverseMapping, outVarsReverseMapping, mgdScript);
		final Term renamed = Substitution.apply(mgdScript, substitutionMapping, rhs);
		return renamed;
	}

	private static Map<Term, Term> computeSubstitutionMapping(final Term rhs, final Term[] conjuncts,
			final TermVariable forbiddenTerm, final Map<TermVariable, IProgramVar> inVarsReverseMapping,
			final Map<TermVariable, IProgramVar> outVarsReverseMapping, final ManagedScript mgdScript)
			throws SimultaneousUpdateException {
		final Map<Term, Term> result = new HashMap<>();
		for (final TermVariable tv : rhs.getFreeVars()) {
			IProgramVar pv = inVarsReverseMapping.get(tv);
			if (pv != null) {
				result.put(tv, pv.getTermVariable());
			} else {
				pv = outVarsReverseMapping.get(tv);
				if (pv != null) {
					final Term renamed = extractUpdateRhs(tv, conjuncts, forbiddenTerm, inVarsReverseMapping,
							outVarsReverseMapping, mgdScript);
					if (renamed == null) {
						throw new SimultaneousUpdateException("cannot bring into simultaneous update form, " + tv
								+ " has two outvars in equality " + Arrays.toString(conjuncts));

					}
					result.put(tv, renamed);
				} else {
					throw new SimultaneousUpdateException("cannot bring into simultaneous update form, " + tv
							+ " has neither invar nor outvar in " + Arrays.toString(conjuncts));
				}
			}
		}
		return result;
	}

	/**
	 * Returns the variables that occur on the right-hand side of updates.
	 */
	public Map<IProgramVar, Term> getDeterministicAssignment() {
		return mDeterministicAssignment;
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
