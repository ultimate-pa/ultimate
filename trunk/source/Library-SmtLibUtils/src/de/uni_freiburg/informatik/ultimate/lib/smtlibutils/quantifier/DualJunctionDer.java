/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Case;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.SolveForSubjectUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.SupportingTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Destructive equality resolution (DER) for conjunctions (resp. disjunctions).
 * <br>
 * The DER elimination technique does the following transformation, where t is a
 * term in which x does not occur and [x-->t] denotes the substitution that
 * replaces all occurrences of x by t.
 *
 * <pre>
 * ∃x. x=t ∧ φ(x)   ⟿⟿⟿      φ[x-->t]
 * ∀x. x≠t ∨ φ(x)   ⟿⟿⟿      φ[x-->t]
 * </pre>
 *
 * If relations do not have the form x=t (resp. x≠t) we use our
 * {@link PolynomialRelation}s and {@link SolvedBinaryRelation}s and try to
 * bring them into this form.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionDer extends DualJunctionQuantifierElimination {

	/**
	 * Checks if banned variable occurs in div. Ignores if variable got div captured
	 * by transformation or occured in div before. <br />
	 * TODO 20210131 Matthias: Might be helpful for debugging. Remove after a few
	 * years if transformation is error-free.
	 */
	private static final boolean DO_OLD_DIV_CAPTURE_CHECK = false;

	/**
	 * @see constructor
	 */
	private final boolean mExpensiveEliminations;

	public enum IntricateOperations {
		NONE, ADDITIONAL_DUAL_JUNCTS, AUXILIARY_VARIABLES, CASE_DISTINCTION,
	}

	/**
	 * @param expensiveEliminations
	 *            If set to true we do expensive eliminations where auxiliary
	 *            variables and case distinctions are allowed. If set to false we do
	 *            only inexpensive eliminations where non of the above is allowed.
	 *            Note that in the first case we will not do all simple
	 *            eliminations. If you want the full elimination power you should
	 *            two instances of this class.
	 */
	public DualJunctionDer(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean expensiveEliminations) {
		super(script, services);
		mExpensiveEliminations = expensiveEliminations;
	}

	@Override
	public String getName() {
		return "destructive equality resolution";
	}

	@Override
	public String getAcronym() {
		return "DER";
	}

	public boolean areExpensiveEliminationsAllowed() {
		return mExpensiveEliminations;
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		final IDerHelper<?>[] helpers;
		if (mExpensiveEliminations) {
			helpers = new IDerHelper[] { new DerHelperMcsbr(IntricateOperations.AUXILIARY_VARIABLES),
//					20221121 Matthias: Omit cases that require case distinction temporarily
//					new DerHelperMcsbr(IntricateOperations.CASE_DISTINCTION)
					};
		} else {
			helpers = new IDerHelper[] { new DerHelperSbr(),
					new DerHelperMcsbr(IntricateOperations.ADDITIONAL_DUAL_JUNCTS) };
		}
		final EliminationResult er = tryExhaustivelyToEliminate(inputEt, helpers);
		if (er != null && false) {
			final XnfDer oldDer = new XnfDer(mMgdScript, mServices);
			final DualJunctionQeAdapter2014 adapter = new DualJunctionQeAdapter2014(mMgdScript, mServices, oldDer);
			final EliminationResult resultOld = adapter.tryToEliminate(inputEt);
			if (!er.getEliminationTask().getEliminatees().equals(resultOld.getEliminationTask().getEliminatees())) {
				throw new AssertionError("Resuts of old and new differ");
			}
		}
		return er;
	}

	/**
	 * Try to iteratively eliminate as many eliminatees as possible using the given
	 * "derHelpers", one after another. Return null if did not make progress for any
	 * eliminatee.
	 */
	public EliminationResult tryExhaustivelyToEliminate(final EliminationTask inputEt,
			final IDerHelper<?>... derHelpers) {
		EliminationTask currentEt = inputEt;
		final LinkedHashSet<TermVariable> aquiredEliminatees = new LinkedHashSet<>();
		while (true) {
			final EliminationResult er = tryToEliminateOne(currentEt, derHelpers);
			if (er == null) {
				// no success, no further iterations
				break;
			}
			aquiredEliminatees.addAll(er.getNewEliminatees());
			currentEt = er.getEliminationTask();
			if (!aquiredEliminatees.isEmpty()) {
				break;
			}
			if (QuantifierUtils.isCorrespondingFiniteJunction(currentEt.getQuantifier(),
					er.getEliminationTask().getTerm())) {
				// we can push the quantifier, no further iterations
				break;
			}
		}
		if (currentEt == inputEt) {
			// only one non-successful iteration
			return null;
		} else {
			return new EliminationResult(currentEt, aquiredEliminatees);
		}
	}

	/**
	 * Try to eliminate some eliminatee using the given "derHelpers", one after
	 * another. Return immediately after the first successful step (note that a step
	 * can be successful if a case distinction was made and the variable was only
	 * eliminated in for some cases). Return null if did not make progress for any
	 * eliminatee.
	 */
	private EliminationResult tryToEliminateOne(final EliminationTask inputEt, final IDerHelper<?>... derHelpers) {
		for (final IDerHelper<?> derHelper : derHelpers) {
			final EliminationResult er = tryExhaustivelyToEliminate(derHelper, inputEt);
			if (er != null) {
				return er;
			}
		}
		return null;
	}

	/**
	 * Try to iteratively eliminate as many eliminatees as possible using the given
	 * "derHelper". Return null if did not make progress for any eliminatee.
	 */
	public EliminationResult tryExhaustivelyToEliminate(final IDerHelper<?> derHelper, final EliminationTask inputEt) {
		EliminationTask currentEt = inputEt;
		final LinkedHashSet<TermVariable> aquiredEliminatees = new LinkedHashSet<>();
		while (true) {
			final EliminationResult er = tryToEliminateOne(derHelper, currentEt);
			if (er == null) {
				// no success, no further iterations
				break;
			}
			aquiredEliminatees.addAll(er.getNewEliminatees());
			currentEt = er.getEliminationTask();
			if (!aquiredEliminatees.isEmpty()) {
				break;
			}
			if (QuantifierUtils.isCorrespondingFiniteJunction(currentEt.getQuantifier(),
					er.getEliminationTask().getTerm())) {
				// we can push the quantifier, no further iterations
				break;
			}
		}
		if (currentEt == inputEt) {
			// only one non-successful iteration
			return null;
		} else {
			return new EliminationResult(currentEt, aquiredEliminatees);
		}
	}

	/**
	 * Try to eliminate some eliminatee using the given "derHelper". Return
	 * immediately after the first successful step (note that a step can be
	 * successful if a case distinction was made and the variable was only
	 * eliminated in for some cases). Return null if did not make progress
	 * for any eliminatee.
	 */
	private EliminationResult tryToEliminateOne(final IDerHelper<?> derHelper, final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final EliminationResult er = derHelper.tryToEliminateSbr(mMgdScript, eliminatee, inputEt);
			if (er != null) {
				return er;
			}
		}
		return null;
	}

	private static Term doSubstitutions(final ManagedScript mgdScript, final int quantifier,
			final List<Term> otherDualJuncts, final SolvedBinaryRelation sbr, final List<Term> dualJunctsResult) {
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(sbr.getLeftHandSide(),
				sbr.getRightHandSide());
		for (final Term otherDualJunct : otherDualJuncts) {
			final Term replaced = Substitution.apply(mgdScript, substitutionMapping, otherDualJunct);
			assert UltimateNormalFormUtils.respectsUltimateNormalForm(replaced) : "Term not in UltimateNormalForm";
			dualJunctsResult.add(replaced);
		}
		final Term dualJunctionResult = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier,
				dualJunctsResult);
		return dualJunctionResult;
	}

	private static boolean eachCaseHasDerRelationSymbol(final MultiCaseSolvedBinaryRelation mcsbr,
			final int quantifier) {
		for (final Case cas : mcsbr.getCases()) {
			if (cas.getSolvedBinaryRelation() != null) {
				if (!QuantifierUtils.isDerRelationSymbol(quantifier,
						cas.getSolvedBinaryRelation().getRelationSymbol())) {
					return false;
				}
			}
		}
		return true;
	}


	public static SolvedBinaryRelation tryPlr(final Script script, final int quantifier, final TermVariable eliminatee,
			final Term atom) {
		final Term rightHandSide;
		if (isSimilarModuloNegation(eliminatee, atom)) {
			rightHandSide = QuantifierUtils.negateIfUniversal(script, quantifier, script.term("true"));
		} else if (isDistinctModuloNegation(eliminatee, atom)) {
			rightHandSide = QuantifierUtils.negateIfUniversal(script, quantifier, script.term("false"));
		} else {
			return null;
		}
		final RelationSymbol relationSymbol = QuantifierUtils.getDerOperator(quantifier);
		return new SolvedBinaryRelation(eliminatee, rightHandSide, relationSymbol);
	}

	public static boolean isSimilarModuloNegation(final Term checkedTerm, final Term wantedTerm) {
		if (wantedTerm.equals(checkedTerm)) {
			return true;
		}
		final Term unzipped = SmtUtils.unzipNot(wantedTerm);
		if (unzipped != null) {
			return isDistinctModuloNegation(checkedTerm, unzipped);
		} else {
			return false;
		}
	}

	public static boolean isDistinctModuloNegation(final Term checkedTerm, final Term wantedTerm) {
		final Term unzipped = SmtUtils.unzipNot(wantedTerm);
		if (unzipped != null) {
			return isSimilarModuloNegation(checkedTerm, unzipped);
		} else {
			return false;
		}
	}


	private static abstract class IDerHelper<SR> {

		public Pair<Integer, SR> findBestReplacementSbr(final ManagedScript mgdScript, final int quantifier,
				final TermVariable eliminatee, final Term[] dualJuncts, final Set<TermVariable> bannedForDivCapture) {
			for (int i = 0; i < dualJuncts.length; i++) {
				if (Arrays.asList(dualJuncts[i].getFreeVars()).contains(eliminatee)) {
					final SR sbr = solveForSubject(mgdScript, quantifier, eliminatee, dualJuncts[i],
							bannedForDivCapture);
					if (sbr != null) {
						return new Pair<Integer, SR>(i, sbr);
					}
				}
			}
			return null;
		}

		protected abstract SR solveForSubject(final ManagedScript mgdScript, final int quantifier, final TermVariable eliminatee,
				final Term term, Set<TermVariable> bannedForDivCapture);

		private EliminationResult tryToEliminateSbr(final ManagedScript mgdScript, final TermVariable eliminatee,
				final EliminationTask et) {
			final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
			final Set<TermVariable> bannedForDivCapture = new HashSet<>(et.getEliminatees());
			bannedForDivCapture.addAll(et.getContext().getBoundByAncestors());
			final Pair<Integer, SR> pair = findBestReplacementSbr(mgdScript, et.getQuantifier(), eliminatee,
					dualJuncts, bannedForDivCapture);
			if (pair == null) {
				return null;
			}
			final List<Term> otherDualJuncts = toListAllButOne(dualJuncts, pair.getFirst());
			return applyReplacement(mgdScript, et, otherDualJuncts, pair.getSecond());
		}

		protected abstract EliminationResult applyReplacement(ManagedScript mgdScript, EliminationTask et,
				List<Term> otherDualJuncts, SR sbr);
	}

	/**
	 * Transforms array to list but omits index idxOmit.
	 */
	private static <E> List<E> toListAllButOne(final E[] array, final int idxOmit) {
		assert 0 <= idxOmit && idxOmit < array.length;
		final List<E> result = new ArrayList<E>(array.length-1);
		for (int i = 0; i<array.length; i++) {
			if (i != idxOmit) {
				result.add(array[i]);
			}
		}
		return result;
	}

	public static class DerHelperSbr extends IDerHelper<SolvedBinaryRelation> {


		public DerHelperSbr() {
			super();
		}

		@Override
		public SolvedBinaryRelation solveForSubject(final ManagedScript mgdScript, final int quantifier,
				final TermVariable eliminatee, final Term term, final Set<TermVariable> bannedForDivCapture) {
			if (SmtSortUtils.isBoolSort(eliminatee.getSort()) && SmtSortUtils.isBoolSort(term.getSort())) {
				final SolvedBinaryRelation sbr = DualJunctionDer.tryPlr(mgdScript.getScript(), quantifier, eliminatee,
						term);
				if (sbr != null) {
					return sbr;
				}
			}
			final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(term);
			if (ber != null && QuantifierUtils.isDerRelationSymbol(quantifier, ber.getRelationSymbol())) {
				final SolvedBinaryRelation sfs = ber.solveForSubject(mgdScript.getScript(), eliminatee);
				if (sfs != null) {
					return sfs;
				}
			}
			final PolynomialRelation pr = PolynomialRelation.of(mgdScript.getScript(), term);
			if (pr == null) {
				return null;
			}
			final SolvedBinaryRelation sfs = pr.solveForSubject(mgdScript.getScript(), eliminatee);
			if (sfs == null) {
				return null;
			}
			if (SolveForSubjectUtils.isVariableDivCaptured(sfs, bannedForDivCapture)) {
				throw new AssertionError("cannot divCaputure with simple solveForSubject");
			}
			if (QuantifierUtils.isDerRelationSymbol(quantifier, sfs.getRelationSymbol())) {
				return sfs;
			} else {
				return null;
			}
		}

		@Override
		protected EliminationResult applyReplacement(final ManagedScript mgdScript, final EliminationTask et,
				final List<Term> otherDualJuncts, final SolvedBinaryRelation sbr) {
			final List<Term> dualJunctsResult = new ArrayList<>();
			final Term dualJunctionResult = doSubstitutions(mgdScript, et.getQuantifier(), otherDualJuncts, sbr,
					dualJunctsResult);
			return new EliminationResult(et.update(dualJunctionResult), Collections.emptySet());
		}
	}

	private static class DerHelperMcsbr extends IDerHelper<MultiCaseSolvedBinaryRelation> {

		private final IntricateOperations mIntricateOperations;

		public DerHelperMcsbr(final IntricateOperations intricateOperations) {
			super();
			mIntricateOperations = intricateOperations;
		}

		@Override
		public MultiCaseSolvedBinaryRelation solveForSubject(final ManagedScript mgdScript, final int quantifier,
				final TermVariable eliminatee, final Term term, final Set<TermVariable> bannedForDivCapture) {
			final PolynomialRelation pr = PolynomialRelation.of(mgdScript.getScript(), term);
			if (pr == null) {
				return null;
			}
			final boolean allowDivModBasedSolution = (mIntricateOperations == IntricateOperations.AUXILIARY_VARIABLES
					|| mIntricateOperations == IntricateOperations.CASE_DISTINCTION);
			final MultiCaseSolvedBinaryRelation mcsbr = pr.solveForSubject(mgdScript, eliminatee,
					Xnf.fromQuantifier(quantifier), bannedForDivCapture, allowDivModBasedSolution);
			if (mcsbr == null) {
				return null;
			}
			switch (mIntricateOperations) {
			case NONE:
				throw new AssertionError();
			case ADDITIONAL_DUAL_JUNCTS:
				if (mcsbr.getCases().size() > 1 || !mcsbr.getAuxiliaryVariables().isEmpty()) {
					return null;
				}
				break;
			case AUXILIARY_VARIABLES:
				if (mcsbr.getCases().size() > 1) {
					return null;
				}
				break;
			case CASE_DISTINCTION:
				// do nothing. Everything is allowed
				break;
			default:
				throw new AssertionError("unknon value " + mIntricateOperations);
			}
			if (DO_OLD_DIV_CAPTURE_CHECK && SolveForSubjectUtils.isVariableDivCaptured(mcsbr, bannedForDivCapture)) {
				throw new AssertionError("variable got div captured");
			}
			if (eachCaseHasDerRelationSymbol(mcsbr, quantifier)) {
				return mcsbr;
			} else {
				return null;
			}
		}

		@Override
		protected EliminationResult applyReplacement(final ManagedScript mgdScript, final EliminationTask et,
				final List<Term> otherDualJuncts, final MultiCaseSolvedBinaryRelation mcsbr) {
			final List<Term> correspondingJunctsResult = new ArrayList<>();
			for (final Case cas : mcsbr.getCases()) {
				final List<Term> dualJunctsResult = new ArrayList<>();
				for (final SupportingTerm st : cas.getSupportingTerms()) {
					dualJunctsResult.add(st.getTerm());
				}
				final Term dualJunctionResult;
				if (cas.getSolvedBinaryRelation() != null) {
					dualJunctionResult = doSubstitutions(mgdScript, et.getQuantifier(), otherDualJuncts,
							cas.getSolvedBinaryRelation(), dualJunctsResult);
				} else {
					dualJunctsResult.addAll(otherDualJuncts);
					dualJunctionResult = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
							et.getQuantifier(), dualJunctsResult);
				}
				correspondingJunctsResult.add(dualJunctionResult);
			}
			final Term correspondingJunction = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(),
					et.getQuantifier(), correspondingJunctsResult);
			return new EliminationResult(et.update(correspondingJunction), mcsbr.getAuxiliaryVariables());
		}
	}


}
