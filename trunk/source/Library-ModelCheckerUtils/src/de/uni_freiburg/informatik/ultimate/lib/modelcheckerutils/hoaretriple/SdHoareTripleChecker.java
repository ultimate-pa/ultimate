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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * Hoare triple checker that uses only simple dataflow analysis to check triples. If this simple analysis is not able to
 * determine the result UNKNOWN is returned.
 *
 * @author Matthias Heizmann
 */
public class SdHoareTripleChecker implements IHoareTripleChecker {
	static final boolean LAZY_CHECKS = false;

	private final HoareTripleCheckerStatisticsGenerator mStatistics;

	private final InternalCheckHelper mInternalCheckHelper;
	private final CallCheckHelper mCallCheckHelper;
	private final ReturnCheckHelper mReturnCheckHelper;

	public SdHoareTripleChecker(final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier) {
		final var coverage = predicateUnifier.getCoverageRelation();
		final IPredicate truePredicate = predicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();

		mStatistics = new HoareTripleCheckerStatisticsGenerator();

		mInternalCheckHelper = new InternalCheckHelper(coverage, falsePredicate, truePredicate, mStatistics,
				csToolkit.getModifiableGlobalsTable());
		mCallCheckHelper = new CallCheckHelper(coverage, falsePredicate, truePredicate, mStatistics,
				csToolkit.getModifiableGlobalsTable());
		mReturnCheckHelper = new ReturnCheckHelper(coverage, falsePredicate, truePredicate, mStatistics,
				csToolkit.getModifiableGlobalsTable());
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return mInternalCheckHelper.check(pre, null, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return mCallCheckHelper.check(pre, null, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		return mReturnCheckHelper.check(preLin, preHier, act, succ);
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getStatistics() {
		return mStatistics;
	}

	@Override
	public void releaseLock() {
		// do nothing, since objects of this class do not lock the solver
	}
}
