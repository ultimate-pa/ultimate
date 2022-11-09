/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicCallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A Hoare triple checker that transfers predicates and actions to a different script before calling an underlying Hoare
 * triple checker.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class TransferringHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mUnderlying;
	private final IPredicateUnifier mUnifier;
	private final TransferrerWithVariableCache mTransferrer;

	/**
	 * Create a new wrapper.
	 *
	 * @param underlying
	 *            The Hoare triple checker that shall be wrapped
	 * @param transferrer
	 *            used to transfer predicates and actions to the given Hoare triple checker's script
	 */
	public TransferringHoareTripleChecker(final IHoareTripleChecker underlying,
			final TransferrerWithVariableCache transferrer, final IPredicateUnifier unifier) {
		mUnderlying = Objects.requireNonNull(underlying);
		mTransferrer = Objects.requireNonNull(transferrer);
		mUnifier = unifier;
	}

	@Override
	public void releaseLock() {
		mUnderlying.releaseLock();
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		final IPredicate transferredPre = transfer(pre);
		final IPredicate transferredPost = transfer(post);
		final IInternalAction transferredAct = new BasicInternalAction(act.getPrecedingProcedure(),
				act.getSucceedingProcedure(), mTransferrer.transferTransFormula(act.getTransformula()));
		return mUnderlying.checkInternal(transferredPre, transferredAct, transferredPost);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		final IPredicate transferredPre = transfer(pre);
		final IPredicate transferredPost = transfer(post);
		final ICallAction transferredAct = new BasicCallAction(act.getPrecedingProcedure(),
				act.getSucceedingProcedure(), mTransferrer.transferTransFormula(act.getLocalVarsAssignment()));
		return mUnderlying.checkCall(transferredPre, transferredAct, transferredPost);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate post) {
		final IPredicate transferredPreLin = transfer(preLin);
		final IPredicate transferredPreHier = transfer(preHier);
		final IPredicate transferredPost = transfer(post);
		final IReturnAction transferredAct = new BasicReturnAction(act.getPrecedingProcedure(),
				act.getSucceedingProcedure(), mTransferrer.transferTransFormula(act.getAssignmentOfReturn()),
				mTransferrer.transferTransFormula(act.getLocalVarsAssignmentOfCall()));
		return mUnderlying.checkReturn(transferredPreLin, transferredPreHier, transferredAct, transferredPost);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	private IPredicate transfer(final IPredicate predicate) {
		return mUnifier.getOrConstructPredicate(mTransferrer.transferPredicate(predicate));
	}
}
