/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Destructive equality resolution (DER) for terms in XNF.
 * <br>
 * DER transforms terms of the form
 * <code>∃x. x=t /\ φ(x)</code>
 * into
 * <code>φ[x-->t]</code>
 * where [x-->t] denotes that all occurrences of x have been replaced.
 * (Applies the dual transformation for universal quantification.)
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class XnfDer extends XjunctPartialQuantifierElimination {

	private final static boolean EXTENDED_DEBUG_OUTPUT = false;

	public XnfDer(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "destructive equality resolution";
	}

	@Override
	public String getAcronym() {
		return "DER";
	}

	@Override
	public boolean resultIsXjunction() {
		return true;
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] dualJuncts, final Set<TermVariable> eliminatees) {
		final ArrayList<TermVariable> eliminateesBefore = new ArrayList<>(eliminatees);
		final HashSet<TermVariable> copyOfeliminatees = new HashSet<>(eliminatees);
		final Term[] resultAtoms = tryToEliminate_EqInfoBased(quantifier, dualJuncts, copyOfeliminatees);
		final Term[] resultAtomsSbr_Based = tryToEliminate_SbrBased(quantifier, dualJuncts, eliminatees);
//		assert (eliminatees.equals(copyOfeliminatees)) : "old " + eliminatees + " new " + copyOfeliminatees;
		if (EXTENDED_DEBUG_OUTPUT) {
			final List<TermVariable> eliminateesAfter = eliminateesBefore.stream().filter(x -> !eliminatees.contains(x))
					.collect(Collectors.toList());
			final String message = "Applied " + getAcronym() + " to " + dualJuncts.length + " "
					+ QuantifierUtils.getNameOfDualJuncts(quantifier) + " and " + eliminateesBefore.size()
					+ "eliminatees: " + eliminateesBefore + " removed "
					+ (eliminateesAfter.isEmpty() ? "nothing" : eliminateesAfter);
			mLogger.info(message);
		}
		return resultAtomsSbr_Based;
	}

	private Term[] tryToEliminate_EqInfoBased(final int quantifier, final Term[] dualJuncts,
			final Set<TermVariable> eliminatees) {

		Term[] resultAtoms = dualJuncts;
		boolean someVariableWasEliminated;
		// an elimination may allow further eliminations
		// repeat the following until no variable was eliminated
		Set<TermVariable> freeVarsInResultAtoms = SmtUtils.getFreeVars(Arrays.asList(resultAtoms));
		do {
			someVariableWasEliminated = false;
			final Iterator<TermVariable> it = eliminatees.iterator();
			while (it.hasNext()) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "eliminating " + eliminatees.size()
							+ " quantified variables from " + dualJuncts.length + " xjuncts");
				}
				final TermVariable tv = it.next();
				if (!freeVarsInResultAtoms.contains(tv)) {
					// case where var does not occur
					it.remove();
					continue;
				}
				final Term[] withoutTv = derSimple(mScript, quantifier, resultAtoms, tv, mLogger);
				if (withoutTv != null) {
					resultAtoms = withoutTv;
					freeVarsInResultAtoms = SmtUtils.getFreeVars(Arrays.asList(resultAtoms));
					it.remove();
					someVariableWasEliminated = true;
				}
			}
		} while (someVariableWasEliminated);
		return resultAtoms;
	}

	private Term[] tryToEliminate_SbrBased(final int quantifier, final Term[] dualJuncts,
			final Set<TermVariable> eliminatees) {
		LinkedHashMap<Term, AffineRelation> term2relation = new LinkedHashMap<>();
		for (final Term dualJunct : dualJuncts) {
			term2relation.put(dualJunct, null);
		}

		boolean someVariableWasEliminated = true;
		// an elimination may allow further eliminations
		// repeat the following until no variable was eliminated
		boolean allowIntegerDivisibilityAssumptions = false;
		Set<TermVariable> freeVarsInResultAtoms = SmtUtils.getFreeVars(term2relation.keySet());
		do {
			if (!someVariableWasEliminated) {
				allowIntegerDivisibilityAssumptions = true;
			}
			someVariableWasEliminated = false;
			final Iterator<TermVariable> it = eliminatees.iterator();
			while (it.hasNext()) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "eliminating " + eliminatees.size()
							+ " quantified variables from " + dualJuncts.length + " xjuncts");
				}
				final TermVariable tv = it.next();
				if (!freeVarsInResultAtoms.contains(tv)) {
					// case where var does not occur
					it.remove();
					continue;
				}
				final LinkedHashMap<Term, AffineRelation> withoutTv;

				if (allowIntegerDivisibilityAssumptions) {
					withoutTv = tryToEliminateOneVarAllowAssumptions(mScript, quantifier, term2relation, tv);
				} else {
					withoutTv = tryToEliminateOneVar(mScript, quantifier, term2relation, tv);
				}
				if (withoutTv != null) {
					term2relation = withoutTv;
					freeVarsInResultAtoms = SmtUtils.getFreeVars(term2relation.keySet());
					it.remove();
					someVariableWasEliminated = true;
					allowIntegerDivisibilityAssumptions = false;
				}
			}
		} while (someVariableWasEliminated || !allowIntegerDivisibilityAssumptions);
		return term2relation.keySet().toArray(new Term[term2relation.keySet().size()]);
	}

	private LinkedHashMap<Term, AffineRelation> tryToEliminateOneVar(final Script script, final int quantifier,
			final LinkedHashMap<Term, AffineRelation> term2relation, final TermVariable tv) {
		// returns probably map in the future
		final Pair<Term, SolvedBinaryRelation> solution = tryToSolveWithoutAssumptionsAndUpdateEntries(script,
				quantifier, term2relation, tv);
		if (solution == null) {
			return null;
		} else {
			return replace(script, term2relation, solution.getSecond(), solution.getFirst());
		}
	}

	private LinkedHashMap<Term, AffineRelation> tryToEliminateOneVarAllowAssumptions(final Script script,
			final int quantifier, final LinkedHashMap<Term, AffineRelation> term2relation, final TermVariable tv) {
		final Map<EnumSet<AssumptionForSolvability>, Pair<SolvedBinaryRelation, Term>> map = tryToSolveAllowAssumptions(
				mScript, quantifier, term2relation, tv);
		if (map.isEmpty()) {
			return null;
		} else {
			final Pair<SolvedBinaryRelation, Term> solution = map
					.get(EnumSet.of(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT));
			if (solution == null) {
				throw new UnsupportedOperationException("Not yet implemented: DER support for " + map.keySet());
			} else {
				final LinkedHashMap<Term, AffineRelation> result = replace(script, term2relation, solution.getFirst(),
						solution.getSecond());
				final Term moduloConstraint = QuantifierUtils.negateIfUniversal(mServices, mMgdScript, quantifier,
						solution.getFirst().getAssumptionsMap()
								.get(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT));
				result.put(moduloConstraint, null);
				return result;
				// throw new AssertionError("Integer divisibility " + sbr.getAssumptionsMap());
			}
		}
	}


	private Pair<Term, SolvedBinaryRelation> tryToSolveWithoutAssumptionsAndUpdateEntries(final Script script,
			final int quantifier, final LinkedHashMap<Term, AffineRelation> term2relation, final TermVariable tv) {
		for (final Entry<Term, AffineRelation> entry : term2relation.entrySet()) {
			if (Arrays.asList(entry.getKey().getFreeVars()).contains(tv)) {
				SolvedBinaryRelation sbr;
				sbr = tryToSolveAndUpdateEntry(script, quantifier, tv, entry);
				if (sbr != null && sbr.getAssumptionsMap().isEmpty()) {
					return new Pair<Term, SolvedBinaryRelation>(entry.getKey(), sbr);
				}
			}
		}
		return null;
	}

	private Map<EnumSet<AssumptionForSolvability>, Pair<SolvedBinaryRelation, Term>> tryToSolveAllowAssumptions(
			final Script script, final int quantifier, final LinkedHashMap<Term, AffineRelation> term2relation,
			final TermVariable tv) {
		final Map<EnumSet<AssumptionForSolvability>, Pair<SolvedBinaryRelation, Term>> result = new HashMap<>();
		for (final Entry<Term, AffineRelation> entry : term2relation.entrySet()) {
			if (entry.getValue() != null) {
				// we must use this method only in a second round, all
				// AffineRelations have been cached
				if (Arrays.asList(entry.getKey().getFreeVars()).contains(tv)) {
					final SolvedBinaryRelation sbr = entry.getValue().solveForSubject(mScript, tv);
					if (sbr != null) {
						final Map<AssumptionForSolvability, Term> assumptions = sbr.getAssumptionsMap();
						if (assumptions.isEmpty()) {
							throw new AssertionError("Assumption-free cases should have been handled before");
						}
						// we overwrite existing sbr with same assumptions
						result.put(EnumSet.copyOf(assumptions.keySet()), new Pair<>(sbr, entry.getKey()));
					}
				}
			}
		}
		return result;
	}


	private LinkedHashMap<Term, AffineRelation> replace(final Script script,
			final LinkedHashMap<Term, AffineRelation> term2relation, final SolvedBinaryRelation sbr,
			final Term termOfSbr) {
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(sbr.getLeftHandSide(),
				sbr.getRightHandSide());
		final LinkedHashMap<Term, AffineRelation> result = new LinkedHashMap<>();
		for (final Entry<Term, AffineRelation> entry : term2relation.entrySet()) {
			if (entry.getKey() == termOfSbr) {
				// skip this entry, it would become equivalent to the neutral
				// element of the logical connective
				continue;
			}
			if (Arrays.asList(entry.getKey().getFreeVars()).contains(sbr.getLeftHandSide())) {
				final Substitution substitution = new SubstitutionWithLocalSimplification(mMgdScript,
						substitutionMapping);
				final Term replaced = substituteAndNormalize(substitution, entry.getKey());
				assert UltimateNormalFormUtils.respectsUltimateNormalForm(replaced) : "Term not in UltimateNormalForm";
				result.put(replaced, null);
			} else {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return result;
	}

	private SolvedBinaryRelation tryToSolveAndUpdateEntry(final Script script, final int quantifier,
			final TermVariable tv, final Entry<Term, AffineRelation> entry) {
		final SolvedBinaryRelation sbr;
		if (entry.getValue() != null) {
			// cached AffineRelation available
			if (!isDerRelation(quantifier, entry.getValue().getRelationSymbol())) {
				sbr = null;
			} else {
				sbr = entry.getValue().solveForSubject(script, tv);
			}
		} else {
			// no cached AffineRelation available
			final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(entry.getKey());
			if (ber == null) {
				return null;
			}
			if (!isDerRelation(quantifier, ber.getRelationSymbol())) {
				sbr = null;
			} else {
				final SolvedBinaryRelation sber = ber.solveForSubject(script, tv);
				if (sber != null) {
					sbr = sber;
				} else {
					final AffineRelation affRel = AffineRelation.convert(script, entry.getKey());
					if (affRel == null) {
						sbr = null;
					} else {
						entry.setValue(affRel);
						sbr = affRel.solveForSubject(script, tv);
					}
				}
			}
		}
		return sbr;
	}

	private static boolean isDerRelation(final int quantifier, final RelationSymbol relationSymbol) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return relationSymbol == RelationSymbol.EQ;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return relationSymbol == RelationSymbol.DISTINCT;
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}

	private SolvedBinaryRelation solveForTvBer(final Script script, final Term key, final TermVariable tv) {
		final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(key);
		final SolvedBinaryRelation res;
		if (ber == null) {
			res = null;
		} else {
			res = ber.solveForSubject(script, tv);
		}
		return res;
	}

	/**
	 * TODO: revise documentation Try to eliminate the variables vars in term. Let vars = {x_1,...,x_n} and term = φ.
	 * Returns a term that is equivalent to ∃x_1,...,∃x_n φ, but were variables are removed. Successfully removed
	 * variables are also removed from vars. Analogously for universal quantification.
	 *
	 * @param logger
	 */
	private Term[] derSimple(final Script script, final int quantifier, final Term[] inputAtoms, final TermVariable tv,
			final ILogger logger) {
		final Term[] resultAtoms;
		final EqualityInformation eqInfo = EqualityInformation.getEqinfo(script, tv, inputAtoms, null, quantifier);
		if (eqInfo == null) {
			logger.debug(new DebugMessage("not eliminated quantifier via DER for {0}", tv));
			resultAtoms = null;
		} else {
			logger.debug(new DebugMessage("eliminated quantifier via DER for {0}", tv));
			resultAtoms = new Term[inputAtoms.length - 1];
			final Map<Term, Term> substitutionMapping =
					Collections.singletonMap(eqInfo.getGivenTerm(), eqInfo.getRelatedTerm());
			final Substitution substitution = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
			for (int i = 0; i < eqInfo.getIndex(); i++) {
				resultAtoms[i] = substituteAndNormalize(substitution, inputAtoms[i]);
				assert UltimateNormalFormUtils
						.respectsUltimateNormalForm(resultAtoms[i]) : "Term not in UltimateNormalForm";
			}
			for (int i = eqInfo.getIndex() + 1; i < inputAtoms.length; i++) {
				resultAtoms[i - 1] = substituteAndNormalize(substitution, inputAtoms[i]);
				assert UltimateNormalFormUtils
						.respectsUltimateNormalForm(resultAtoms[i - 1]) : "Term not in UltimateNormalForm";
			}
		}
		return resultAtoms;
	}

	/**
	 * Apply substitution to term and normalize afterwards if the substitution modified the term.
	 */
	private Term substituteAndNormalize(final Substitution substitution, final Term term) {
		Term result = substitution.transform(term);
		if (term != result) {
			final AffineRelation afr = AffineRelation.convert(mScript, result);
			if (afr != null) {
				result = afr.positiveNormalForm(mScript);
			}
		}
		return result;
	}

}
