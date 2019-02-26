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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IncrementalPlicationChecker.Plication;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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
	final IncrementalPlicationChecker iea;

	public ArrayIndexEqualityManager(final ThreeValuedEquivalenceRelation<Term> tver, final Term context, final int quantifier, final ILogger logger, final ManagedScript mgdScript) {
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
		iea = new IncrementalPlicationChecker(plication, mMgdScript, mContext);
		final Term absorbingElement = QuantifierUtils.getNeutralElement(mMgdScript.getScript(), mQuantifier);
		final Validity validity = iea.checkPlication(absorbingElement);
		if (validity == Validity.VALID) {
			mContextIsAbsorbingElement = true;
		} else {
			mContextIsAbsorbingElement = false;
		}
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
			if (mAlreadyCheckedBySolver.containsPair(elem1Rep, elem2Rep)) {
				return EqualityStatus.UNKNOWN;
			}
			checkEqualityStatusViaSolver(mQuantifier, mTver, iea, elem1Rep, elem2Rep);
			mAlreadyCheckedBySolver.addPair(elem1Rep, elem2Rep);
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
			final IncrementalPlicationChecker iea, final Term index1,
			final Term index2) throws AssertionError {
		final Term eq = SmtUtils.binaryEquality(mMgdScript.getScript(), index1, index2);
		if (SmtUtils.isTrue(eq)) {
			tver.reportEquality(index1, index2);
			assert !tver.isInconsistent() : "inconsistent equality information";
		} else if (SmtUtils.isFalse(eq)) {
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
					tver.reportEquality(index1, index2);
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
					mLogger.warn("solver failed to check if following not equals relation is implied: "
							+ eq);
				}

				if (notEqualsHolds == Validity.VALID) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						tver.reportDisequality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						tver.reportEquality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else {
						throw new AssertionError("unknown quantifier");
					}
					mLogger.info("detected not equals via solver");
				}
			}
		}
	}

	public void unlockSolver() {
		iea.unlockSolver();
	}

	public boolean contextIsAbsorbingElement() {
		return mContextIsAbsorbingElement;
	}

	public EqualityStatus checkIndexEquality(final ArrayIndex selectIndex, final ArrayIndex storeIndex) {
		for (int i=0; i<selectIndex.size(); i++) {
			final EqualityStatus eqStaus = checkEqualityStatus(selectIndex.get(i), storeIndex.get(i));
			if (eqStaus == EqualityStatus.NOT_EQUAL || eqStaus == EqualityStatus.UNKNOWN) {
				return eqStaus;
			}
		}
		return EqualityStatus.EQUAL;
	}


	public Term constructPairwiseEquality(final ArrayIndex index1, final ArrayIndex index2) {
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

	public Term constructDerRelation(final Script script, final int quantifier, final ArrayIndex index1,
			final ArrayIndex index2) {
		assert index1.size() == index2.size();
		final ArrayList<Term> dualJuncts = new ArrayList<>(index1.size());
		for (int i = 0; i < index1.size(); i++) {
			dualJuncts.add(QuantifierUtils.applyDerOperator(script, quantifier, index1.get(i), index2.get(i)));
		}
		return QuantifierUtils.applyDualFiniteConnective(script, quantifier, dualJuncts);
	}

	public Term constructAntiDerRelation(final Script script, final int quantifier, final ArrayIndex index1,
			final ArrayIndex index2) {
		assert index1.size() == index2.size();
		final ArrayList<Term> sameJuncts = new ArrayList<>(index1.size());
		for (int i = 0; i < index1.size(); i++) {
			sameJuncts.add(QuantifierUtils.applyAntiDerOperator(script, quantifier, index1.get(i), index2.get(i)));
		}
		return QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, sameJuncts);
	}


}
