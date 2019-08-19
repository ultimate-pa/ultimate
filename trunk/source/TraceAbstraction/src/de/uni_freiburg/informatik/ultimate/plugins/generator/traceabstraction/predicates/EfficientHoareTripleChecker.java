/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

public class EfficientHoareTripleChecker implements IHoareTripleChecker {
	private static final boolean REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED = true;
	private static final boolean REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED = true;

	private final IHoareTripleChecker mSmtBasedHoareTripleChecker;
	private final SdHoareTripleChecker mSdHoareTripleChecker;
	private final IHoareTripleChecker mHoareTripleCheckerForReview;

	public EfficientHoareTripleChecker(final IHoareTripleChecker smtBasedHoareTripleChecker,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier) {
		super();
		mSmtBasedHoareTripleChecker = new ProtectiveHoareTripleChecker(smtBasedHoareTripleChecker, predicateUnifier);
		mSdHoareTripleChecker = new SdHoareTripleChecker(csToolkit, predicateUnifier,
				mSmtBasedHoareTripleChecker.getEdgeCheckerBenchmark());
		mHoareTripleCheckerForReview = new MonolithicHoareTripleChecker(csToolkit);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkInternal(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED) {
				assert reviewInductiveInternal(pre, act, succ, sdResult);
			}
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkInternal(pre, act, succ);
		if (REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED) {
			assert reviewInductiveInternal(pre, act, succ, result);
		}
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkCall(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED) {
				assert reviewInductiveCall(pre, act, succ, sdResult);
			}
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkCall(pre, act, succ);
		if (REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED) {
			assert reviewInductiveCall(pre, act, succ, result);
		}
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED) {
				assert reviewInductiveReturn(preLin, preHier, act, succ, sdResult);
			}
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		if (REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED) {
			assert reviewInductiveReturn(preLin, preHier, act, succ, result);
		}
		return result;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mSmtBasedHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	private boolean reviewInductiveInternal(final IPredicate state, final IInternalAction act, final IPredicate succ,
			final Validity result) {
		releaseLock();
		final Validity reviewResult = mHoareTripleCheckerForReview.checkInternal(state, act, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		}
		throw createAssertionError(result, reviewResult);
	}

	private boolean reviewInductiveCall(final IPredicate state, final ICallAction act, final IPredicate succ,
			final Validity result) {
		releaseLock();
		final Validity reviewResult = mHoareTripleCheckerForReview.checkCall(state, act, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		}
		throw createAssertionError(result, reviewResult);

	}

	private boolean reviewInductiveReturn(final IPredicate state, final IPredicate hier, final IReturnAction act,
			final IPredicate succ, final Validity result) {
		releaseLock();
		final Validity reviewResult = mHoareTripleCheckerForReview.checkReturn(state, hier, act, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		}
		throw createAssertionError(result, reviewResult);
	}

	private static AssertionError createAssertionError(final Validity result, final Validity reviewResult) {
		return new AssertionError("Result: " + result + "  Review result: " + reviewResult);
	}

	/**
	 * Return true if results are compatible or one is UNKNOWN
	 */
	private static boolean resultCompatibleHelper(final Validity validity1, final Validity validity2) {
		switch (validity1) {
		case VALID:
			return validity2 == Validity.VALID || validity2 == Validity.UNKNOWN;
		case INVALID:
			return validity2 == Validity.INVALID || validity2 == Validity.UNKNOWN;
		case UNKNOWN:
		case NOT_CHECKED:
			return true;
		default:
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public void releaseLock() {
		mSmtBasedHoareTripleChecker.releaseLock();
	}

}
