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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class EfficientIgnoringHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mSmtBasedHoareTripleChecker;
	private final IHoareTripleChecker mSdHoareTripleChecker;
	private final Set<? extends IAction> mProtectedActions;

	public EfficientIgnoringHoareTripleChecker(final IHoareTripleChecker smtBasedHoareTripleChecker,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier,
			final Set<? extends IAction> protectedActions, final boolean allowSdForProtectedActions) {

		mProtectedActions = protectedActions;

		final Predicate<IPredicate> predPredicateProtection = predicateUnifier::isIntricatePredicate;
		final Predicate<IAction> predActionProtection = mProtectedActions::contains;
		mSmtBasedHoareTripleChecker = new ProtectiveHoareTripleChecker(smtBasedHoareTripleChecker, predicateUnifier,
				predPredicateProtection, predActionProtection);
		mSdHoareTripleChecker = new ProtectiveHoareTripleChecker(
				new SdHoareTripleChecker(csToolkit, predicateUnifier,
						mSmtBasedHoareTripleChecker.getEdgeCheckerBenchmark()),
				predicateUnifier, a -> true, allowSdForProtectedActions ? a -> true : predActionProtection);

	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkInternal(pre, act, succ);
		if (sdResult != Validity.UNKNOWN && sdResult != Validity.NOT_CHECKED) {
			return sdResult;
		}
		return mSmtBasedHoareTripleChecker.checkInternal(pre, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkCall(pre, act, succ);
		if (sdResult != Validity.UNKNOWN && sdResult != Validity.NOT_CHECKED) {
			return sdResult;
		}
		return mSmtBasedHoareTripleChecker.checkCall(pre, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		final Validity sdResult = mSdHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		if (sdResult != Validity.UNKNOWN && sdResult != Validity.NOT_CHECKED) {
			return sdResult;
		}
		return mSmtBasedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
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
