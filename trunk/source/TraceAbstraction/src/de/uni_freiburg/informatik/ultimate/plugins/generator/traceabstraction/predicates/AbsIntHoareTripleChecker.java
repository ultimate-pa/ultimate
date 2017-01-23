/*
 * Copyright (C) 2016-2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * {@link IHoareTripleChecker} that performs hoare triple checks using an abstract post operator.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntHoareTripleChecker<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL>
		implements IHoareTripleChecker {

	private final ILogger mLogger;
	private final IAbstractPostOperator<STATE, ACTION, VARDECL> mPostOp;
	private final IAbstractStateBinaryOperator<STATE> mMergeOp;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IPredicateUnifier mPredicateUnifier;
	private final HoareTripleCheckerStatisticsGenerator mBenchmark;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;

	public AbsIntHoareTripleChecker(final IUltimateServiceProvider services,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IAbstractPostOperator<STATE, ACTION, VARDECL> postOp, final IPredicateUnifier predicateUnifer) {
		mDomain = Objects.requireNonNull(domain);
		mPostOp = Objects.requireNonNull(postOp);
		mMergeOp = Objects.requireNonNull(mDomain.getMergeOperator());

		// TODO: Implement AbsIntPredicate unifier and use it as parameter instead of the normal
		// PredicateUnifier
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBenchmark = new HoareTripleCheckerStatisticsGenerator();
		mTruePred = mPredicateUnifier.getTruePredicate();
		mFalsePred = mPredicateUnifier.getFalsePredicate();
	}

	private Validity checkNonReturnTransition(final STATE preState, final ACTION act, final STATE postState) {
		if (preState == null) {
			// this is a dirty hack to signify a top state -- creation of top states wont work until we got rid of
			// variables
			return Validity.UNKNOWN;
		}
		if (postState == null) {
			// see above
			return Validity.VALID;
		}

		if (preState.isBottom()) {
			return Validity.VALID;
		}

		try {
			final STATE calculatedPost = mPostOp.apply(preState, act).stream().reduce(mMergeOp::apply).orElse(null);
			if (postState.isBottom()) {
				if (calculatedPost == null || calculatedPost.isBottom()) {
					return trackPost(Validity.VALID, act);
				}
				return Validity.UNKNOWN;
			}

			final SubsetResult subs = postState.isSubsetOf(calculatedPost);
			if (subs != SubsetResult.NONE) {
				return trackPost(Validity.VALID, act);
			}
			return Validity.UNKNOWN;
		} catch (final Throwable t) {
			// dirty hack
			return Validity.UNKNOWN;
		}
	}

	private Validity trackPost(final Validity valid, final ACTION act) {
		if (act instanceof ICallAction) {
			return trackCallPost(valid);
		} else if (act instanceof IReturnAction) {
			return trackReturnPost(valid);
		} else {
			return trackInternalPost(valid);
		}
	}

	private Validity trackCallPost(final Validity valid) {
		if (valid == Validity.UNKNOWN) {
			mBenchmark.getSolverCounterUnknown().incCa();
		} else if (valid == Validity.VALID) {
			mBenchmark.getSolverCounterUnsat().incCa();
		}
		return valid;
	}

	private Validity trackInternalPost(final Validity valid) {
		if (valid == Validity.UNKNOWN) {
			mBenchmark.getSolverCounterUnknown().incIn();
		} else if (valid == Validity.VALID) {
			mBenchmark.getSolverCounterUnsat().incIn();
		}
		return valid;
	}

	private Validity trackReturnPost(final Validity valid) {
		if (valid == Validity.UNKNOWN) {
			mBenchmark.getSolverCounterUnknown().incRe();
		} else if (valid == Validity.VALID) {
			mBenchmark.getSolverCounterUnsat().incRe();
		}
		return valid;
	}

	private Validity checkReturnTransition(final STATE preLinState, final STATE preHierState, final ACTION act,
			final STATE postState) {
		if (preLinState.isBottom()) {
			return Validity.VALID;
		}

		if (preHierState.isBottom()) {
			return Validity.VALID;
		}

		try {
			final STATE calculatedPost =
					mPostOp.apply(preLinState, preHierState, act).stream().reduce(mMergeOp::apply).orElse(null);

			if (postState.isBottom()) {
				if (calculatedPost == null || calculatedPost.isBottom()) {
					return trackPost(Validity.VALID, act);
				}
				return Validity.INVALID;
			}

			final SubsetResult subs = postState.isSubsetOf(calculatedPost);
			if (subs != SubsetResult.NONE) {
				return trackPost(Validity.VALID, act);
			}
			return Validity.UNKNOWN;
		} catch (final Throwable e) {
			// dirty hack
			return Validity.UNKNOWN;
		}
	}

	@Override
	public void releaseLock() {
		// no lock needed
	}

	@SuppressWarnings("unchecked")
	private STATE getState(final IPredicate pred) {
		if (pred instanceof AbsIntPredicate<?, ?>) {
			return ((AbsIntPredicate<STATE, ?>) pred).getAbstractState();
		} else if (pred == mTruePred) {
			return null;
		} else if (pred == mFalsePred) {
			return mDomain.createBottomState();
		} else {
			throw new UnsupportedOperationException("Cannot handle non-absint predicates");
		}
	}

	@SuppressWarnings("unchecked")
	private ACTION getAction(final IAction act) {
		return (ACTION) act;
	}

	private Validity checkNonReturn(final IPredicate prePred, final IAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final STATE pre = getState(prePred);
		final STATE succ = getState(succPred);
		final ACTION action = getAction(act);
		final Validity rtr = checkNonReturnTransition(pre, action, succ);
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return checkNonReturn(pre, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return checkNonReturn(pre, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLinPred, final IPredicate preHierPred, final IReturnAction act,
			final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();

		final STATE preLin = getState(preLinPred);
		final STATE preHier = getState(preHierPred);
		final STATE succ = getState(succPred);
		final ACTION action = getAction(act);

		final Validity rtr = checkReturnTransition(preLin, preHier, action, succ);
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mBenchmark;
	}
}
