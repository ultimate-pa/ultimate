/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class TermTransferringIndependenceRelation<L extends IAction> implements IIndependenceRelation<IPredicate, L> {
	private static final boolean ABSTRACT_TF_WITH_BRANCH_ENCODERS = false;

	private final IIndependenceRelation<IPredicate, L> mUnderlying;
	private final TransferrerWithVariableCache mTransferrer;
	private final ICopyActionFactory<L> mCopyFactory;
	private final boolean mTransferOnlyConditions;

	public TermTransferringIndependenceRelation(final IIndependenceRelation<IPredicate, L> underlying,
			final TransferrerWithVariableCache transferrer, final ICopyActionFactory<L> copyFactory,
			final boolean transferOnlyConditions) {
		mUnderlying = underlying;
		mTransferrer = transferrer;
		mCopyFactory = copyFactory;
		mTransferOnlyConditions = transferOnlyConditions;

		assert !transferOnlyConditions || mUnderlying.isConditional() : "Nothing to transfer";
		assert transferOnlyConditions || mCopyFactory != null : "cannot transfer letters without factory";
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public Dependence isIndependent(final IPredicate state, final L a, final L b) {
		final var aTransferred = transfer(a);
		final var bTransferred = transfer(b);
		final IPredicate transferredState = state == null ? null : mTransferrer.transferPredicate(state);
		return mUnderlying.isIndependent(transferredState, aTransferred, bTransferred);
	}

	@Override
	public ISymbolicIndependenceRelation<L, IPredicate> getSymbolicRelation() {
		final var underlying = mUnderlying.getSymbolicRelation();
		if (underlying == null) {
			return null;
		}
		return new SymbolicTransferringIndependence(underlying);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	private final L transfer(final L letter) {
		if (mTransferOnlyConditions) {
			return letter;
		}

		final var tf = mTransferrer.transferTransFormula(letter.getTransformula());
		UnmodifiableTransFormula tfWithBE;
		if (ABSTRACT_TF_WITH_BRANCH_ENCODERS && letter instanceof IActionWithBranchEncoders) {
			final var originalTfWithBE = ((IActionWithBranchEncoders) letter).getTransitionFormulaWithBranchEncoders();
			if (originalTfWithBE != null) {
				tfWithBE = mTransferrer.transferTransFormula(originalTfWithBE);
			} else {
				tfWithBE = null;
			}
		} else {
			tfWithBE = null;
		}
		return mCopyFactory.copy(letter, tf, tfWithBE);
	}

	private class SymbolicTransferringIndependence implements ISymbolicIndependenceRelation<L, IPredicate> {
		private final ISymbolicIndependenceRelation<L, IPredicate> mUnderlyingSymbolic;

		public SymbolicTransferringIndependence(final ISymbolicIndependenceRelation<L, IPredicate> underlying) {
			mUnderlyingSymbolic = underlying;
		}

		@Override
		public IPredicate getCommutativityCondition(final IPredicate condition, final L a, final L b) {
			final var aTransferred = transfer(a);
			final var bTransferred = transfer(b);
			final var conditionTransferred =
					!isConditional() || condition == null ? null : mTransferrer.transferPredicate(condition);
			final var generatedCondition =
					mUnderlyingSymbolic.getCommutativityCondition(conditionTransferred, aTransferred, bTransferred);
			if (generatedCondition == null) {
				return null;
			}
			return mTransferrer.backTransferPredicate(generatedCondition);
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlying.isSymmetric();
		}

		@Override
		public boolean isConditional() {
			return mUnderlyingSymbolic.isConditional();
		}
	}
}
