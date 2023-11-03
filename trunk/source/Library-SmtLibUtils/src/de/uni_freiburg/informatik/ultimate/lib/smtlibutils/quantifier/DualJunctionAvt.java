/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiIndexArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Replace term of the form `∃x. a' = (store a k x) ∧ ϕ[x]` by `a'= (store a k
 * (select a' k)) ∧ ϕ[(select a' k)]` <br />
 * TODO Use {@link ArrayIndexEqualityManager} to simplify index equalities
 * immediately.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionAvt extends DualJunctionQuantifierElimination {

	private final boolean mAllowCaseDistinctions;

	public DualJunctionAvt(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean allowCaseDistinctions) {
		super(script, services);
		mAllowCaseDistinctions = allowCaseDistinctions;
	}

	@Override
	public String getName() {
		return "array value transformation";
	}

	@Override
	public String getAcronym() {
		return "AVT";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		final boolean maybeApplicable = inexpensivePreinvestigation(inputEt);
		if (!maybeApplicable) {
			return null;
		}

		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final AvtReplacementInformation replacementInfo = findReplacement(inputEt, eliminatee);
			if (replacementInfo != null) {
				if (replacementInfo.getIndicesOfSubsequentArrayWrites().isEmpty() || mAllowCaseDistinctions) {
					return doElimination(inputEt, eliminatee, replacementInfo);
				}
			}
		}
		return null;
	}

	private EliminationResult doElimination(final EliminationTask inputEt, final TermVariable eliminatee,
			final AvtReplacementInformation replacementInfo) {
		final MultiIndexArrayUpdate miau = replacementInfo.getMiau();
		final ArrayIndex indexOfEliminateeWrite = miau.getMultiDimensionalNestedStore().getIndices()
				.get(replacementInfo.getPositionOfWriteWhereEliminateeIsWritten());

		final List<Term> correspondingFiniteJunction = new ArrayList<>();

		for (final ArrayIndex idx : replacementInfo.getIndicesOfSubsequentArrayWrites()) {
			final Term specialCase = constructDualFiniteJunctionForCoincidingIndexCase(inputEt.getQuantifier(), miau,
					indexOfEliminateeWrite, idx, replacementInfo.getPositionOfWriteWhereEliminateeIsWritten(),
					replacementInfo.getOtherDualFiniteJuncts());
			correspondingFiniteJunction.add(specialCase);
		}

		final Term defaultCase = constructDualFiniteJunctionForCaseForDefaultCase(inputEt.getQuantifier(),
				inputEt.getTerm(), eliminatee, replacementInfo.getReplacement(), indexOfEliminateeWrite,
				replacementInfo.getIndicesOfSubsequentArrayWrites());
		correspondingFiniteJunction.add(defaultCase);

		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, inputEt.getQuantifier(),
				correspondingFiniteJunction);
		final EliminationTask resultEt = new EliminationTask(inputEt.getQuantifier(), inputEt.getEliminatees(), result,
				inputEt.getContext());
		return new EliminationResult(resultEt, Collections.emptySet());
	}

	/**
	 * It may be costly to always iterate over all eliminatees and dualFiniteJuncts.
	 * In many cases there will be no MultiIndexArrayUpdate. In order to save these
	 * costs we use this methods to check in advance of some eliminatee occurs in
	 * the value of some MultiIndexArrayUpdate. <br />
	 * It seems to make sense to let this method return more information and use
	 * this later. However, this would make the code significantly more complex and
	 * we can only save some time in the rare cases where this preinvestigation
	 * returns true.
	 */
	private boolean inexpensivePreinvestigation(final EliminationTask inputEt) {
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		for (int j = 0; j < dualFiniteJuncts.length; j++) {
			final MultiIndexArrayUpdate miau = MultiIndexArrayUpdate.of(mScript, dualFiniteJuncts[j]);
			if (miau == null) {
				continue;
			}
			if (!QuantifierUtils.getDerOperator(inputEt.getQuantifier()).equals(miau.getRelationSymbol())) {
				continue;
			}
			for (int i = miau.getMultiDimensionalNestedStore().getIndices().size() - 1; i >= 0; i--) {
				final Term valueAtI = miau.getMultiDimensionalNestedStore().getValues().get(i);
				if (DataStructureUtils.haveNonEmptyIntersection(Arrays.asList(valueAtI.getFreeVars()),
						inputEt.getEliminatees())) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Construct term for case where the index of some subsequent write is
	 * equivalent ("different" for universal quantification) to the index where the
	 * eliminatee is written. In this case, we can just drop the array write at the
	 * position where the index is written.
	 */
	private Term constructDualFiniteJunctionForCoincidingIndexCase(final int quantifier,
			final MultiIndexArrayUpdate asMiau, final ArrayIndex indexOfEliminateeWrite, final ArrayIndex idx,
			final int positionOfWriteWhereEliminateeIsWritten, final List<Term> otherDualFiniteJuncts) {
		final MultiIndexArrayUpdate newMiau = asMiau.removeOneIndex(positionOfWriteWhereEliminateeIsWritten);
		final List<Term> dualFiniteJuncts = new ArrayList<>();
		dualFiniteJuncts.add(constructDerRelationForIndices(mScript, quantifier, indexOfEliminateeWrite, idx));
		dualFiniteJuncts.addAll(otherDualFiniteJuncts);
		dualFiniteJuncts.add(newMiau.toTerm(mScript));
		return QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, dualFiniteJuncts);
	}

	/**
	 * Construct term where the eliminatee is substituted by the replacement term
	 * and we assume that the index of each subsequent write is different
	 * ("equivalent" for universal quantification) from the index at which the
	 * eliminatee is written.
	 */
	private Term constructDualFiniteJunctionForCaseForDefaultCase(final int quantifier, final Term inputTerm,
			final TermVariable eliminatee, final Term replacement, final ArrayIndex indexOfEliminateeWrite,
			final List<ArrayIndex> indicesOfSubsequentWrites) {
		final List<Term> dualFiniteJuncts = new ArrayList<>();
		for (final ArrayIndex subsequentWriteIndex : indicesOfSubsequentWrites) {
			dualFiniteJuncts.add(constructAntiDerRelationForIndices(mScript, quantifier, indexOfEliminateeWrite,
					subsequentWriteIndex));
		}
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(eliminatee, replacement);
		dualFiniteJuncts.add(Substitution.apply(mMgdScript, substitutionMapping, inputTerm));
		return QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, dualFiniteJuncts);
	}

	public static Term constructDerRelationForIndices(final Script script, final int quantifier,
			final ArrayIndex index1, final ArrayIndex index2) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return ArrayIndex.constructIndexEquality(script, index1, index2);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return ArrayIndex.constructIndexNotEquals(script, index1, index2);
		} else {
			throw new AssertionError("IllegalQuantifier");
		}
	}

	public Term constructAntiDerRelationForIndices(final Script script, final int quantifier, final ArrayIndex index1,
			final ArrayIndex index2) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return ArrayIndex.constructIndexNotEquals(script, index1, index2);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return ArrayIndex.constructIndexEquality(script, index1, index2);
		} else {
			throw new AssertionError("IllegalQuantifier");
		}
	}

	/**
	 * @return Triple such that
	 *         <li>the first entry is the index of the dualJunct in which we can
	 *         eliminate the eliminatee
	 *         <li>the second entry is the number of the write of the
	 *         {@link MultiIndexArrayUpdate} is written
	 *         <li>the third entry is a term that is logically equivalent to the
	 *         eliminatee in case subsequent writes to the array were done at
	 *         indices that are different from the index where the eliminatee is
	 *         written
	 */
	private AvtReplacementInformation findReplacement(final EliminationTask inputEt, final TermVariable eliminatee) {

		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		for (int j = 0; j < dualFiniteJuncts.length; j++) {
			final MultiIndexArrayUpdate miau = MultiIndexArrayUpdate.of(mScript, dualFiniteJuncts[j]);
			if (miau == null) {
				continue;
			}
			if (!QuantifierUtils.getDerOperator(inputEt.getQuantifier()).equals(miau.getRelationSymbol())) {
				continue;
			}
			for (int i = miau.getMultiDimensionalNestedStore().getIndices().size() - 1; i >= 0; i--) {
				final Term valueAtI = miau.getMultiDimensionalNestedStore().getValues().get(i);
				if (Arrays.asList(valueAtI.getFreeVars()).contains(eliminatee)) {
					final ArrayIndex idx = miau.getMultiDimensionalNestedStore().getIndices().get(i);
					final Term selectFromNewArray = new MultiDimensionalSelect(miau.getNewArray(), idx).toTerm(mScript);
					final Term derRelation = QuantifierUtils.applyDerOperator(mScript, inputEt.getQuantifier(),
							valueAtI, selectFromNewArray);
					final SolvedBinaryRelation sbr = new DualJunctionDer.DerHelperSbr().solveForSubject(mMgdScript,
							inputEt.getQuantifier(), eliminatee, derRelation,
							inputEt.getContext().getBoundByAncestors());
					if (sbr != null) {
						assert sbr.getLeftHandSide() == eliminatee;
						final List<Term> otherDualFiniteJuncts = DataStructureUtils
								.copyAllButOne(Arrays.asList(dualFiniteJuncts), j);
						return new AvtReplacementInformation(miau, i, otherDualFiniteJuncts, sbr.getRightHandSide());
					}
				}
			}
		}
		return null;
	}

	private class AvtReplacementInformation {
		private final MultiIndexArrayUpdate mMiau;
		private final int mPositionOfWriteWhereEliminateeIsWritten;
		private final List<ArrayIndex> mIndicesOfSubsequentArrayWrites;
		private final List<Term> mOtherDualFiniteJuncts;
		private final Term mReplacement;

		public AvtReplacementInformation(final MultiIndexArrayUpdate miau,
				final int positionOfWriteWhereEliminateeIsWritten, final List<Term> otherDualFiniteJuncts,
				final Term replacement) {
			mMiau = miau;
			mPositionOfWriteWhereEliminateeIsWritten = positionOfWriteWhereEliminateeIsWritten;
			mIndicesOfSubsequentArrayWrites = indicesOfSubsequentArrayWrites(positionOfWriteWhereEliminateeIsWritten,
					miau);
			mOtherDualFiniteJuncts = otherDualFiniteJuncts;
			mReplacement = replacement;
		}

		private List<ArrayIndex> indicesOfSubsequentArrayWrites(final int positionOfWriteWhereEliminateeIsWritten,
				final MultiIndexArrayUpdate miau) {
			final List<ArrayIndex> indicesOfSubsequentWrites = new ArrayList<>();
			for (int i = positionOfWriteWhereEliminateeIsWritten + 1; i < miau.getMultiDimensionalNestedStore()
					.getIndices().size(); i++) {
				final ArrayIndex idx = miau.getMultiDimensionalNestedStore().getIndices().get(i);
				indicesOfSubsequentWrites.add(idx);
			}
			return indicesOfSubsequentWrites;
		}

		public MultiIndexArrayUpdate getMiau() {
			return mMiau;
		}

		public int getPositionOfWriteWhereEliminateeIsWritten() {
			return mPositionOfWriteWhereEliminateeIsWritten;
		}

		public List<ArrayIndex> getIndicesOfSubsequentArrayWrites() {
			return mIndicesOfSubsequentArrayWrites;
		}

		public List<Term> getOtherDualFiniteJuncts() {
			return mOtherDualFiniteJuncts;
		}

		public Term getReplacement() {
			return mReplacement;
		}

	}
}
