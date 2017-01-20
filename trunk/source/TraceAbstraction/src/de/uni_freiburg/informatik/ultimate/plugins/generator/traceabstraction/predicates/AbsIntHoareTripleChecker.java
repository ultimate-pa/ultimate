/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * Hoare triple checker that computes predicates that are obtained from abstract interpretation in a lazy, cached
 * fashion.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntHoareTripleChecker<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL>
		implements IHoareTripleChecker {

	private final ILogger mLogger;
	private final IAbstractPostOperator<STATE, ACTION, VARDECL> mPostOp;
	private final IAbstractStateBinaryOperator<STATE> mMergeOp;
	private final IPredicateUnifier mPredicateUnifier;

	public AbsIntHoareTripleChecker(final IUltimateServiceProvider services,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain, final IPredicateUnifier predicateUnifer) {
		final IAbstractDomain<STATE, ACTION, VARDECL> localDomain = Objects.requireNonNull(domain);
		mPostOp = Objects.requireNonNull(localDomain.getPostOperator());
		mMergeOp = Objects.requireNonNull(localDomain.getMergeOperator());
		// TODO: Implement AbsIntPredicate unifier and use it as parameter instead of the normal
		// PredicateUnifier
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	private Validity checkNonReturnTransition(final AbsIntPredicate<STATE, VARDECL> pre, final ACTION act,
			final AbsIntPredicate<STATE, VARDECL> succ) {

		final STATE preState = pre.getAbstractState();
		if (preState.isBottom()) {
			return Validity.VALID;
		}
		final STATE postState = succ.getAbstractState();

		final STATE calculatedPost = mPostOp.apply(preState, act).stream().reduce(mMergeOp::apply).orElse(null);
		if (postState.isBottom()) {
			if (calculatedPost == null) {
				return Validity.VALID;
			}
			return Validity.INVALID;
		}

		final SubsetResult subs = postState.isSubsetOf(calculatedPost);
		if (subs != SubsetResult.NONE) {
			return Validity.VALID;
		}
		return Validity.UNKNOWN;
	}

	private Validity checkReturnTransition(final AbsIntPredicate<STATE, VARDECL> preLin,
			final AbsIntPredicate<STATE, VARDECL> preHier, final ACTION act,
			final AbsIntPredicate<STATE, VARDECL> succ) {
		final STATE preLinState = preLin.getAbstractState();
		if (preLinState.isBottom()) {
			return Validity.VALID;
		}

		final STATE preHierState = preHier.getAbstractState();
		if (preHierState.isBottom()) {
			return Validity.VALID;
		}

		final STATE postState = succ.getAbstractState();

		final STATE calculatedPost =
				mPostOp.apply(preLinState, preHierState, act).stream().reduce(mMergeOp::apply).orElse(null);
		if (postState.isBottom()) {
			if (calculatedPost == null) {
				return Validity.VALID;
			}
			return Validity.INVALID;
		}

		final SubsetResult subs = postState.isSubsetOf(calculatedPost);
		if (subs != SubsetResult.NONE) {
			return Validity.VALID;
		}
		return Validity.UNKNOWN;
	}

	@Override
	public void releaseLock() {
		// no lock needed
	}

	@SuppressWarnings("unchecked")
	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return checkNonReturnTransition((AbsIntPredicate<STATE, VARDECL>) pre, (ACTION) act,
				(AbsIntPredicate<STATE, VARDECL>) succ);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return checkNonReturnTransition((AbsIntPredicate<STATE, VARDECL>) pre, (ACTION) act,
				(AbsIntPredicate<STATE, VARDECL>) succ);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		return checkReturnTransition((AbsIntPredicate<STATE, VARDECL>) preLin,
				(AbsIntPredicate<STATE, VARDECL>) preHier, (ACTION) act, (AbsIntPredicate<STATE, VARDECL>) succ);
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		// we dont do benchmarking
		return null;
	}
}
