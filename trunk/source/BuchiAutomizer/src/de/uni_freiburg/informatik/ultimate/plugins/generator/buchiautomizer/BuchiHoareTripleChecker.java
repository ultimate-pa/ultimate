/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * HoareTripleChecker that is aware of the special rankDecrease predicates 
 * (e.g., the Honda Predicate). If one of these Predicates occurs on the 
 * left-hand side of a Hoare triple check (i.e., is Precondition or HierPred) 
 * we have to replace it by the corresponding rankEqual predicate.
 * 
 * E.g., f(x)<oldrk /\ oldrk>=0 is replaced by f(x)<=oldrk.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiHoareTripleChecker implements IHoareTripleChecker {

	private final Map<IPredicate,IPredicate> mRankDecrease2RankEquality = 
			new HashMap<IPredicate,IPredicate>();
	private final IHoareTripleChecker mIHoareTripleChecker;

	
	public BuchiHoareTripleChecker(IHoareTripleChecker iHoareTripleChecker) {
		super();
		mIHoareTripleChecker = iHoareTripleChecker;
	}


	public void putDecreaseEqualPair(IPredicate rankDecreaseAndBound, IPredicate rankEquality) {
		mRankDecrease2RankEquality.put(rankDecreaseAndBound, rankEquality);
	}

	
	private IPredicate replaceIfRankDecreasePredicate(IPredicate p) {
		final IPredicate rankEq = mRankDecrease2RankEquality.get(p);
		if (rankEq == null) {
			return p;
		} else {
			return rankEq;
		}
	}
	
	
	@Override
	public Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ) {
		pre = replaceIfRankDecreasePredicate(pre);
		return mIHoareTripleChecker.checkInternal(pre, act, succ);
	}

	@Override
	public Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ) {
		pre = replaceIfRankDecreasePredicate(pre);
		return mIHoareTripleChecker.checkCall(pre, act, succ);
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			IReturnAction act, IPredicate succ) {
		preLin = replaceIfRankDecreasePredicate(preLin);
		preHier = replaceIfRankDecreasePredicate(preHier);
		return mIHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
	}


	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mIHoareTripleChecker.getEdgeCheckerBenchmark();
	}


	@Override
	public void releaseLock() {
		mIHoareTripleChecker.releaseLock();
	}
	

}
