/*
 * Copyright (C) 2015-2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * {@link IHoareTripleChecker} that "protects" another {@link IHoareTripleChecker} from Hoare triples satisfying some
 * condition expressed by {@link Predicate}s over {@link IPredicate}s (for pre, post, and hierachical pre conditions)
 * and {@link IAction} (for all actions of the Hoare triple). If the Hoare triple that should be checked satisfies such
 * a condition, we return {@link Validity#NOT_CHECKED}. Otherwise we ask the "protected" {@link IHoareTripleChecker}.
 *
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ProtectiveHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mProtectedHoareTripleChecker;
	private final Predicate<IPredicate> mPredicateProtection;
	private final Predicate<IAction> mActionProtection;
	private final Term mTrueTerm;
	private final Term mFalseTerm;

	/**
	 * see {@link ProtectiveHoareTripleChecker}
	 */
	public ProtectiveHoareTripleChecker(final IHoareTripleChecker protectedHoareTripleChecker,
			final IPredicateUnifier predicateUnifier, final Predicate<IPredicate> predPredicateProtection,
			final Predicate<IAction> predActionProtection) {
		mProtectedHoareTripleChecker = protectedHoareTripleChecker;
		mPredicateProtection = predPredicateProtection;
		mActionProtection = predActionProtection;
		mTrueTerm = predicateUnifier.getTruePredicate().getClosedFormula();
		mFalseTerm = predicateUnifier.getFalsePredicate().getClosedFormula();
	}

	/**
	 * Create an {@link IHoareTripleChecker} that "protects" another {@link IHoareTripleChecker} from intricate
	 * predicates provided by an {@link IPredicateUnifier}.
	 *
	 * If the Hoare triple that should be checked contains an intricate predicate we return
	 * {@link Validity#NOT_CHECKED}. Otherwise we ask the "protected" IHoareTripleChecker.
	 */
	public static ProtectiveHoareTripleChecker protectionFromIntricatePredicates(
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifier) {
		final Predicate<IPredicate> predPredicateProtection = predicateUnifier::isIntricatePredicate;
		final Predicate<IAction> predActionProtection = a -> true;
		return new ProtectiveHoareTripleChecker(protectedHoareTripleChecker, predicateUnifier, predPredicateProtection,
				predActionProtection);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		if (isTrueTrue(pre, succ) || isFalse(pre)) {
			return Validity.VALID;
		}
		if (mPredicateProtection.test(pre) || mPredicateProtection.test(succ) || mActionProtection.test(act)) {
			return Validity.NOT_CHECKED;
		}
		return mProtectedHoareTripleChecker.checkInternal(pre, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		if (isTrueTrue(pre, succ) || isFalse(pre)) {
			return Validity.VALID;
		}
		if (mPredicateProtection.test(pre) || mPredicateProtection.test(succ) || mActionProtection.test(act)) {
			return Validity.NOT_CHECKED;
		}
		return mProtectedHoareTripleChecker.checkCall(pre, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		if (isTrueTrue(preLin, preHier, succ) || isFalse(preLin, preHier)) {
			return Validity.VALID;
		}
		if (mPredicateProtection.test(preLin) || mPredicateProtection.test(preHier) || mPredicateProtection.test(succ)
				|| mActionProtection.test(act)) {
			return Validity.NOT_CHECKED;
		}
		return mProtectedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mProtectedHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return mProtectedHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		mProtectedHoareTripleChecker.releaseLock();
	}

	private boolean isTrueTrue(final IPredicate pre, final IPredicate post) {
		return pre.getClosedFormula() == mTrueTerm && post.getClosedFormula() == mTrueTerm;
	}

	private boolean isTrueTrue(final IPredicate preLin, final IPredicate preHier, final IPredicate post) {
		return preLin.getClosedFormula() == mTrueTerm && preHier.getClosedFormula() == mTrueTerm
				&& post.getClosedFormula() == mTrueTerm;
	}

	private boolean isFalse(final IPredicate preLin, final IPredicate preHier) {
		return preLin.getClosedFormula() == mFalseTerm || preHier.getClosedFormula() == mFalseTerm;
	}

	private boolean isFalse(final IPredicate pre) {
		return pre.getClosedFormula() == mFalseTerm;
	}
}
