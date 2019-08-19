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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * IHoareTripleChecker that "protects" another IHoareTripleChecker from intricate predicates. The mPredicateUnifer
 * defines what an intricate predicates is. If the Hoare triple that should be checked contains an intricate predicate
 * we return Validity.NOT_CHECKED. Otherwise we ask the "protected" IHoareTripleChecker.
 *
 * @author Matthias Heizmann
 *
 */
public class ProtectiveHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mProtectedHoareTripleChecker;
	private final IPredicateUnifier mPredicateUnifer;

	public ProtectiveHoareTripleChecker(final IHoareTripleChecker protectedHoareTripleChecker,
			final IPredicateUnifier predicateUnifer) {
		super();
		mProtectedHoareTripleChecker = protectedHoareTripleChecker;
		mPredicateUnifer = predicateUnifer;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		if (mPredicateUnifer.isIntricatePredicate(pre) || mPredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		}
		return mProtectedHoareTripleChecker.checkInternal(pre, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		if (mPredicateUnifer.isIntricatePredicate(pre) || mPredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		}
		return mProtectedHoareTripleChecker.checkCall(pre, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		if (mPredicateUnifer.isIntricatePredicate(preLin) || mPredicateUnifer.isIntricatePredicate(preHier)
				|| mPredicateUnifer.isIntricatePredicate(succ)) {
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
}
