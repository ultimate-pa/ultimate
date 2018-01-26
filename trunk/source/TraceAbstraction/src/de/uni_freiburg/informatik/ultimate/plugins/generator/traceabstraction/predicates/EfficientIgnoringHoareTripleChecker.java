/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class EfficientIgnoringHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mSmtBasedHoareTripleChecker;
	private final SdHoareTripleChecker mSdHoareTripleChecker;
	private final boolean mAllowSdForProtectedActions;
	private final Set<? extends IAction> mProtectedActions;

	public EfficientIgnoringHoareTripleChecker(final IHoareTripleChecker smtBasedHoareTripleChecker,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier,
			final Set<? extends IAction> protectedActions, final boolean allowSdForProtectedActions) {
		mSmtBasedHoareTripleChecker = new ProtectiveHoareTripleChecker(smtBasedHoareTripleChecker, predicateUnifier);
		mSdHoareTripleChecker = new SdHoareTripleChecker(csToolkit, predicateUnifier,
				mSmtBasedHoareTripleChecker.getEdgeCheckerBenchmark());
		mAllowSdForProtectedActions = allowSdForProtectedActions;
		mProtectedActions = protectedActions;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		if (mProtectedActions.contains(act)) {
			if (mAllowSdForProtectedActions) {
				return mSdHoareTripleChecker.checkInternal(pre, act, succ);
			}
			return Validity.NOT_CHECKED;
		}

		final Validity sdResult = mSdHoareTripleChecker.checkInternal(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkInternal(pre, act, succ);
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		if (mProtectedActions.contains(act)) {
			if (mAllowSdForProtectedActions) {
				return mSdHoareTripleChecker.checkCall(pre, act, succ);
			}
			return Validity.NOT_CHECKED;
		}
		final Validity sdResult = mSdHoareTripleChecker.checkCall(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkCall(pre, act, succ);
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		if (mProtectedActions.contains(act)) {
			if (mAllowSdForProtectedActions) {
				return mSdHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
			}
			return Validity.NOT_CHECKED;
		}
		final Validity sdResult = mSdHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			return sdResult;
		}
		final Validity result = mSmtBasedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		return result;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mSmtBasedHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	@Override
	public void releaseLock() {
		mSmtBasedHoareTripleChecker.releaseLock();
	}

}
