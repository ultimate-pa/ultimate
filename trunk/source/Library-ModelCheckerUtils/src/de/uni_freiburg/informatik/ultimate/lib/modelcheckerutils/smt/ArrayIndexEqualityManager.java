/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.IncrementalPlicationChecker.Plication;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class ArrayIndexEqualityManager {

	private final ThreeValuedEquivalenceRelation<Term> mTver;
	private final Term mContext;
	private final boolean mContextIsAbsorbingElement;
	private final Set<TermVariable> mFreeVarsOfContext;
	private final boolean mCheckEqualityStatusOnDemand;
	private final int mQuantifier;
	private final ManagedScript mMgdScript;
	private final ILogger mLogger;
	private final HashRelation<Term, Term> mAlreadyCheckedBySolver;
	final IncrementalPlicationChecker mIea;

	public ArrayIndexEqualityManager(final ThreeValuedEquivalenceRelation<Term> tver, final Term context,
			final int quantifier, final ILogger logger, final ManagedScript mgdScript) {
		super();
		mTver = tver;
		mContext = context;
		mQuantifier = quantifier;
		mLogger = logger;
		mMgdScript = mgdScript;
		mFreeVarsOfContext = Arrays.stream(mContext.getFreeVars()).collect(Collectors.toSet());
		mCheckEqualityStatusOnDemand = true;
		mAlreadyCheckedBySolver = new HashRelation<>();

		final Plication plication;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			plication = Plication.IMPLICATION;
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			plication = Plication.EXPLICATION;
		} else {
			throw new AssertionError("unknown quantifier");
		}
		mIea = new IncrementalPlicationChecker(plication, mMgdScript, mContext);
		final Term absorbingElement = QuantifierUtils.getNeutralElement(mMgdScript.getScript(), mQuantifier);
		final Validity validity = mIea.checkPlication(absorbingElement);
		if (validity == Validity.VALID) {
			mContextIsAbsorbingElement = true;
		} else {
			mContextIsAbsorbingElement = false;
		}
	}

	/**
	 * Find out if the HashRelation mAlreadyCheckedBySolver stores only Terms that
	 * are representatives of the ThreeValuedEquivalenceRelation.
	 */
	boolean alreadyCheckedUsesRepresenatives() {
		for (final Term t : mAlreadyCheckedBySolver.getDomain()) {
			if (!mTver.isRepresentative(t)) {
				return false;
			}
		}
		return true;
	}

	public EqualityStatus checkEqualityStatus(final Term elem1, final Term elem2) {
		if (!allFreeVarsOccurInContext(elem1)) {
			return EqualityStatus.UNKNOWN;
		}
		if (!allFreeVarsOccurInContext(elem2)) {
			return EqualityStatus.UNKNOWN;
		}
		mTver.addElement(elem1);
		mTver.addElement(elem2);
		final EqualityStatus status = mTver.getEqualityStatus(elem1, elem2);
		if (status == EqualityStatus.UNKNOWN && mCheckEqualityStatusOnDemand) {
			final Term elem1Rep = mTver.getRepresentative(elem1);
			final Term elem2Rep = mTver.getRepresentative(elem2);
			assert alreadyCheckedUsesRepresenatives() : "the mAlreadyCheckedBySolver relation is outdated";
			if (mAlreadyCheckedBySolver.containsPair(elem1Rep, elem2Rep)) {
				return EqualityStatus.UNKNOWN;
			}
			mAlreadyCheckedBySolver.addPair(elem1Rep, elem2Rep);
			mAlreadyCheckedBySolver.addPair(elem2Rep, elem1Rep);
			checkEqualityStatusViaSolver(mQuantifier, mTver, mIea, elem1Rep, elem2Rep);
			assert alreadyCheckedUsesRepresenatives() : "the mAlreadyCheckedBySolver relation is outdated";
			return mTver.getEqualityStatus(elem1Rep, elem2Rep);
		}
		return status;
	}

	private boolean allFreeVarsOccurInContext(final Term term) {
		for (final TermVariable tv : term.getFreeVars()) {
			if (!mFreeVarsOfContext.contains(tv)) {
				return false;
			}
		}
		return true;
	}

	private void checkEqualityStatusViaSolver(final int mQuantifier, final ThreeValuedEquivalenceRelation<Term> tver,
			final IncrementalPlicationChecker iea, final Term index1, final Term index2) throws AssertionError {
		final Term eq = SmtUtils.binaryEquality(mMgdScript.getScript(), index1, index2);
		if (SmtUtils.isTrueLiteral(eq)) {
			reportEquality(index1, index2);
			assert !tver.isInconsistent() : "inconsistent equality information";
		} else if (SmtUtils.isFalseLiteral(eq)) {
			tver.reportDisequality(index1, index2);
			assert !tver.isInconsistent() : "inconsistent equality information";
		} else {
			final Term neq = SmtUtils.not(mMgdScript.getScript(), eq);
			final Validity isEqual = iea.checkPlication(eq);
			if (isEqual == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
				mLogger.warn("solver failed to check if following equality is implied: " + eq);
			}
			if (isEqual == Validity.VALID) {
				if (mQuantifier == QuantifiedFormula.EXISTS) {
					reportEquality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else if (mQuantifier == QuantifiedFormula.FORALL) {
					tver.reportDisequality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else {
					throw new AssertionError("unknown quantifier");
				}
				mLogger.info("detected equality via solver");
			} else {
				final Validity notEqualsHolds = iea.checkPlication(neq);
				if (notEqualsHolds == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
					mLogger.warn("solver failed to check if following not equals relation is implied: " + eq);
				}

				if (notEqualsHolds == Validity.VALID) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						tver.reportDisequality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						reportEquality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else {
						throw new AssertionError("unknown quantifier");
					}
					mLogger.info("detected not equals via solver");
				}
			}
		}
	}

	/**
	 * Report to the ThreeValuedEquivalenceRelation that both input Terms are
	 * equivalent. As a consequence, equivalence classes will be merged. This method
	 * also updates the mAlreadyCheckedBySolver HashRelation in order to maintain
	 * the class invariant that mAlreadyCheckedBySolver stores only representatives.
	 */
	private void reportEquality(final Term index1, final Term index2) {
		final Term t1rep = mTver.getRepresentative(index1);
		final Term t2rep = mTver.getRepresentative(index2);
		mTver.reportEquality(index1, index2);
		Term newRepresentative;
		Term outdatedRepresentative;
		if (t1rep == mTver.getRepresentative(index1)) {
			newRepresentative = t1rep;
			outdatedRepresentative = t2rep;
			assert t1rep == mTver.getRepresentative(index2);
		} else {
			newRepresentative = t2rep;
			outdatedRepresentative = t1rep;
			assert t2rep == mTver.getRepresentative(index1);
		}
		final HashRelation<Term, Term> outdatedEntries = new HashRelation<>();
		for (final Entry<Term, Term> entry : mAlreadyCheckedBySolver.entrySet()) {
			if (entry.getKey() == outdatedRepresentative || entry.getValue() == outdatedRepresentative) {
				outdatedEntries.addPair(entry.getKey(), entry.getValue());
			}
		}
		for (final Entry<Term, Term> entry : outdatedEntries.entrySet()) {
			if (entry.getKey() == outdatedRepresentative) {
				final boolean removed = mAlreadyCheckedBySolver.removePair(outdatedRepresentative, entry.getValue());
				if (!removed) {
					throw new AssertionError("element does not exist");
				}
				mAlreadyCheckedBySolver.addPair(newRepresentative, entry.getValue());
			} else if (entry.getValue() == outdatedRepresentative) {
				final boolean removed = mAlreadyCheckedBySolver.removePair(entry.getKey(), outdatedRepresentative);
				if (!removed) {
					throw new AssertionError("element does not exist");
				}
				mAlreadyCheckedBySolver.addPair(entry.getKey(), newRepresentative);
			} else {
				throw new AssertionError("some element has to be outdated.");
			}
		}
	}

	public void unlockSolver() {
		mIea.unlockSolver();
	}

	public boolean contextIsAbsorbingElement() {
		return mContextIsAbsorbingElement;
	}

	public EqualityStatus checkIndexEquality(final ArrayIndex selectIndex, final ArrayIndex storeIndex) {
		for (int i = 0; i < selectIndex.size(); i++) {
			final EqualityStatus eqStaus = checkEqualityStatus(selectIndex.get(i), storeIndex.get(i));
			if (eqStaus == EqualityStatus.NOT_EQUAL || eqStaus == EqualityStatus.UNKNOWN) {
				return eqStaus;
			}
		}
		return EqualityStatus.EQUAL;
	}

	public Term constructIndexEquality(final ArrayIndex index1, final ArrayIndex index2) {
		assert index1.size() == index2.size();
		final ArrayList<Term> conjuncts = new ArrayList<>(index1.size());
		for (int i = 0; i < index1.size(); i++) {
			final EqualityStatus indexEquality = checkEqualityStatus(index1.get(i), index2.get(i));
			switch (indexEquality) {
			case EQUAL:
				// do nothing
				break;
			case NOT_EQUAL:
				return mMgdScript.getScript().term("false");
			case UNKNOWN:
				conjuncts.add(SmtUtils.binaryEquality(mMgdScript.getScript(), index1.get(i), index2.get(i)));
				break;
			default:
				throw new AssertionError();
			}
		}
		return SmtUtils.and(mMgdScript.getScript(), conjuncts);
	}

	/**
	 * <ul>
	 * <li>t1 == t2 for existential quantifier and
	 * <li>t1 != t2 for universal quantifier
	 * </ul>
	 */
	public Term constructDerRelation(final Script script, final int quantifier, final Term t1, final Term t2) {
		final EqualityStatus eq = checkEqualityStatus(t1, t2);
		final Term result;
		switch (eq) {
		case EQUAL:
			result = QuantifierUtils.getAbsorbingElement(script, quantifier);
			break;
		case NOT_EQUAL:
			result = QuantifierUtils.getNeutralElement(script, quantifier);
			break;
		case UNKNOWN:
			result = QuantifierUtils.applyDerOperator(script, quantifier, t1, t2);
			break;
		default:
			throw new AssertionError();
		}
		return result;
	}

	/**
	 * <ul>
	 * <li>t1 != t2 for existential quantifier and
	 * <li>t1 == t2 for universal quantifier
	 * </ul>
	 */
	public Term constructAntiDerRelation(final Script script, final int quantifier, final Term t1, final Term t2) {
		final EqualityStatus eq = checkEqualityStatus(t1, t2);
		final Term result;
		switch (eq) {
		case EQUAL:
			result = QuantifierUtils.getNeutralElement(script, quantifier);
			break;
		case NOT_EQUAL:
			result = QuantifierUtils.getAbsorbingElement(script, quantifier);
			break;
		case UNKNOWN:
			result = QuantifierUtils.applyDerOperator(script, quantifier, t1, t2);
			break;
		default:
			throw new AssertionError();
		}
		return result;
	}

	/**
	 * <ul>
	 * <li>idx1 == idx2 for existential quantifier and
	 * <li>idx1 != idx2 for universal quantifier
	 * </ul>
	 */
	public Term constructDerRelation(final Script script, final int quantifier, final ArrayIndex idx1,
			final ArrayIndex idx2) {
		assert idx1.size() == idx2.size();
		final ArrayList<Term> dualJuncts = new ArrayList<>(idx1.size());
		for (int i = 0; i < idx1.size(); i++) {
			final EqualityStatus entryEquality = checkEqualityStatus(idx1.get(i), idx2.get(i));
			switch (entryEquality) {
			case EQUAL:
				// do nothing
				break;
			case NOT_EQUAL:
				return QuantifierUtils.getNeutralElement(script, quantifier);
			case UNKNOWN:
				dualJuncts.add(QuantifierUtils.applyDerOperator(script, quantifier, idx1.get(i), idx2.get(i)));
				break;
			default:
				throw new AssertionError();
			}
		}
		return QuantifierUtils.applyDualFiniteConnective(script, quantifier, dualJuncts);
	}

	/**
	 * <ul>
	 * <li>idx1 != idx2 for existential quantifier and
	 * <li>idx1 == idx2 for universal quantifier
	 * </ul>
	 */
	public Term constructAntiDerRelation(final Script script, final int quantifier, final ArrayIndex idx1,
			final ArrayIndex idx2) {
		assert idx1.size() == idx2.size();
		final ArrayList<Term> sameJuncts = new ArrayList<>(idx1.size());
		for (int i = 0; i < idx1.size(); i++) {
			final EqualityStatus entryEquality = checkEqualityStatus(idx1.get(i), idx2.get(i));
			switch (entryEquality) {
			case EQUAL:
				// do nothing
				break;
			case NOT_EQUAL:
				return QuantifierUtils.getAbsorbingElement(script, quantifier);
			case UNKNOWN:
				sameJuncts.add(QuantifierUtils.applyAntiDerOperator(script, quantifier, idx1.get(i), idx2.get(i)));
				break;
			default:
				throw new AssertionError();
			}
		}
		return QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, sameJuncts);
	}

	/**
	 * Given one "reference index" idx_ref, a list of indices idx1,...,idxn and two
	 * values val1, val2, construct the following formula.
	 *
	 * <ul>
	 * <li>(idx == luidx1 ∨ ... ∨ idx == idxn ∨ idx != uidx ∨ (select arrRes idx) ==
	 * uval) for existential quantifier and
	 * <li>(idx != luidx1 ∧ ... ∧ idx != idxn ∧ idx == uidx ∧ (select arrRes idx) !=
	 * uval) for universal quantifier
	 * </ul>
	 *
	 * @param laterUpdateIndices
	 *            indices that occur later in the nested stores, outermost at the
	 *            last position
	 */
	private Term constructNestedStoreUpdateConstraintForOnePosition(final Script script, final int quantifier,
			final Term arrayRes, final ArrayIndex idx, final List<ArrayIndex> laterUpdateIndices,
			final ArrayIndex updateIndex, final Term updateValue) {
		final List<Term> correspondingFiniteJuncts = laterUpdateIndices.stream()
				.map(x -> constructDerRelation(script, quantifier, idx, x)).collect(Collectors.toList());
		final Term correspondingFiniteJunction = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier,
				correspondingFiniteJuncts);
		if (correspondingFiniteJunction == QuantifierUtils.getAbsorbingElement(script, quantifier)) {
			// already true (resp. false), no need to construct remaining
			// disjuncts (resp. conjuncts)
			return correspondingFiniteJunction;
		}
		final Term idxAntiDerUidx = constructAntiDerRelation(script, quantifier, idx, updateIndex);
		final MultiDimensionalSelect idxCellOfArrayRes = new MultiDimensionalSelect(arrayRes, idx, script);
		final Term updateValueDerRelation = constructDerRelation(script, quantifier, idxCellOfArrayRes.toTerm(script),
				updateValue);
		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier,
				correspondingFiniteJunction, idxAntiDerUidx, updateValueDerRelation);
		return result;
	}

	/**
	 *
	 * @param storeIndices
	 *            in order of the stores, innermost first, outermost last
	 * @param storeValues
	 *            in order of the stores, innermost first, outermost last
	 */
	public Term constructNestedStoreUpdateConstraint(final Script script, final int quantifier, final Term resArray,
			final ArrayIndex idx, final List<ArrayIndex> storeIndices, final List<Term> storeValues,
			final Term defaultValue) {
		assert storeIndices.size() == storeValues.size();
		final List<Term> resultDualJuncts = new ArrayList<>();
		// if different from all store indices
		// resArray[idx] == defaultValue
		final Term inputCase = constructNestedStoreUpdateConstraintForOnePosition(script, quantifier, resArray, idx,
				storeIndices, idx, defaultValue);
		resultDualJuncts.add(inputCase);
		// if different from all store indices but the innermost
		// resArray[idx] is equivalent to the innermost value
		// if different from all outer store indices but the second innermost
		// resArray[idx] is equivalent to the second innermost value
		// ...
		final LinkedList<ArrayIndex> tmp = new LinkedList<>(storeIndices);
		for (int i = 0; i < storeIndices.size(); i++) {
			final ArrayIndex innermost = tmp.removeFirst();
			final Term correspondingValue = storeValues.get(i);
			final Term term = constructNestedStoreUpdateConstraintForOnePosition(script, quantifier, resArray, idx, tmp,
					innermost, correspondingValue);
			resultDualJuncts.add(term);
		}
		final Term result = QuantifierUtils.applyDualFiniteConnective(script, quantifier, resultDualJuncts);
		return result;
	}

}
