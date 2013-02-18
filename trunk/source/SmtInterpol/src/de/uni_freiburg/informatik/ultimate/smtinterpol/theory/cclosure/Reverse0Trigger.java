/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.Deque;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext.ReactivationContext;


public abstract class Reverse0Trigger extends NonYieldTrigger {
	
	protected int m_reverseNum;
	
	public Reverse0Trigger(int reverseNum) {
		m_reverseNum = reverseNum;
	}
	
	/**
	 * Sets the reactivation context.
	 * @param engine
	 * @param tec
	 * @param match The match we have.
	 * @param set   The term we want to register on.
	 * @param checkblocked
	 * @return <code>true</code> if and only if the reactivation record was
	 * already present and we should block.
	 */
	protected boolean setReactivation(CClosure engine,
			TriggerExecutionContext tec,CCTerm match,CCTerm set,
			boolean checkblocked) {
		ReactivationContext rc = tec.getRC(match);
		if (rc == null)
			rc = tec.createRC(engine, match);
		if (!rc.isRegistered()) {
			rc.register(engine);
			CCParentInfo pa = set.repStar.ccpars.createInfo(0);
//			pa.addReverseTrigger(rc);
		} else
			return false;//checkblocked;
		return false;
	}
	
	private TriggerExecutionContext singleMatch(CClosure engine,List<CCTrigger> path,int pathpos,
			CCTerm[] regs,CCAppTerm match,TriggerExecutionContext tec,
			boolean checkblocked, UpdatableCongruenceBlocker blocker) {
		if (setReactivation(engine,tec,match,match.func,checkblocked))
			return null;
		if (m_reverseNum == 0) {
			assert(!match.isFunc);
			int size = next.getExpectedInputRegisterLength();
			CCTerm[] nextinput = produceOutput(regs, match, size, blocker);
			if (nextinput == null)
				return null;
			TriggerExecutionContext nextTec =
				tec.successor(nextinput, next);
			next.match(engine, nextinput, path, pathpos, nextTec,
					nextTec.getCandidates());
			return null;
		} else {
			assert(match.isFunc);
			assert(next instanceof Reverse0Trigger);
			TriggerExecutionContext nextTec = tec.successor(regs, next);
			for (Parent pa : match.repStar.ccpars.getParentInfo(0))
				nextTec.addCandidate(pa);
			return nextTec;
		}
	}
	
	@Override
	public void match(CClosure engine, CCTerm[] regs, List<CCTrigger> path,
			int pathpos, TriggerExecutionContext tec,Deque<Object> candidates) {
		boolean checkblocked = checkBlocked(path, pathpos);
		HashSet<CCTerm> uniq = new HashSet<CCTerm>();
		TriggerExecutionContext nextTec = null;
		UpdatableCongruenceBlocker blocker = null;
		blocker = tec.getBlocker();
		if (!candidates.isEmpty())
			blocker.update();
		while (!candidates.isEmpty()) {
			Parent pac = (Parent) candidates.removeFirst();
			if (pac.isMarked())
				continue;
			CCAppTerm candidate = pac.getData();
			if (uniq.add(candidate.repStar)) {
				nextTec = singleMatch(engine, path, pathpos, regs ,candidate, 
						tec, checkblocked, blocker);
			}
		}
		blocker.done();
		if (nextTec != null)
			next.match(engine, regs, path, pathpos, nextTec,
					nextTec.getCandidates());
	}

	public String toString() {
		return "Reverse0 "+m_reverseNum;
	}

	protected abstract int getNonReverse0InputLength();
	protected abstract CCTerm[] produceOutput(CCTerm[] regs, CCAppTerm match,
			int size, UpdatableCongruenceBlocker blocker);
	protected abstract UpdatableCongruenceBlocker getBlocker(
			TriggerExecutionContext tec);

	@Override
	public boolean getsCandidates() {
		return true;
	}
	
}
