/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

class InternalCheckHelper extends SdHoareTripleCheckHelper {
	private final SdHoareTripleCheckerHelper mHelper;

	InternalCheckHelper(final IPredicateCoverageChecker coverage, final SdHoareTripleCheckerHelper helper,
			final IPredicate falsePredicate, final IPredicate truePredicate) {
		super(coverage, falsePredicate, truePredicate);
		mHelper = helper;
	}

	@Override
	public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
		assert preHier == null;
		return mHelper.sdecInternalToFalse(preLin, (IInternalAction) act);
	}

	@Override
	public boolean isInductiveSefloop(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ) {
		assert preHier == null;
		return preLin == succ && mHelper.sdecInternalSelfloop(preLin, (IInternalAction) act) == Validity.VALID;
	}

	@Override
	public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IAction act, final IPredicate succ) {
		assert preHier == null;
		return mHelper.sdecInternal(preLin, (IInternalAction) act, succ);
	}

	@Override
	public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ) {
		assert preHier == null;
		return mHelper.sdLazyEcInternal(preLin, (IInternalAction) act, succ);
	}
}