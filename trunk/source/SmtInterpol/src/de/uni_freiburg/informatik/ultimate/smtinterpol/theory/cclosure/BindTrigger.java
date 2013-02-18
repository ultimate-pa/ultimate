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

import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext.ReactivationContext;


// TODO What can we block here? Since we miss the exact merge/unmerge operation
// sequence, we cannot cache all matches and prevent "re-matching" on the same
// (or a congruent) term.
/**
 * A bind instruction.
 * @author Jochen Hoenicke, Juergen Christ
 */
public class BindTrigger extends NonYieldTrigger {
	
	int m_EqRegNum;
	int m_Symb;
	int[] m_RegCtl;
	
	/**
	 * Create a bind instruction.
	 * @param engine	CGraph management engine.
	 * @param eqRegNum Register index containing the desired equivalence class 
	 * 					of the function application.
	 * @param symbol   Function symbol of the application to search.
	 * @param regCtl   Register control: {0: Function Symbol, 1-... Args}.
	 * 					-1 means "Drop the value"
	 */
	public BindTrigger(CClosure engine,int eqRegNum,
			FunctionSymbol symbol,int[] regCtl) {
		this(engine,eqRegNum,symbol,regCtl,null);
	}
	
	/**
	 * Create a bind instruction.
	 * @param engine	CGraph management engine.
	 * @param eqRegNum Register index containing the desired equivalence class 
	 * 					of the function application.
	 * @param symbol   Function symbol of the application to search.
	 * @param regCtl   Register control: {0: Function Symbol, 1-... Args}.
	 * 					-1 means "Drop the value"
	 * @param next		The next instruction to execute after this bind.
	 */
	public BindTrigger(CClosure engine,int eqRegNum,
			FunctionSymbol symbol,int[] regCtl,CCTrigger next) {
		super(next);
		assert regCtl.length == symbol.getParameterCount() + 1 : 
			"Need register control for function symbol and all arguments";
		m_EqRegNum = eqRegNum;
		m_Symb = engine.getFuncTerm(symbol).parentPosition + 
			symbol.getParameterCount() - 1;
		m_RegCtl = regCtl;
	}

	private CCTerm[] produceOutput(CCTerm[] input,CCAppTerm match,int size) {
		CCTerm[] output = Arrays.copyOf(input, size);
		if (m_RegCtl[0] != -1)
			output[m_RegCtl[0]] = match;
		CCAppTerm cur = match;
		// We have register transfer control for app and all args
		for (int i = m_RegCtl.length - 1; i > 1; --i) {
			int ctl = m_RegCtl[i];
			if (ctl != -1)
				output[ctl] = cur.arg;
			cur = (CCAppTerm)cur.func;
		}
		// Prevent ClassCastException in loop above
		if (m_RegCtl[1] != -1) {
			output[m_RegCtl[1]] = cur.arg;
		}
		return output;
	}
	
	private boolean setReactivation(CClosure engine,
			TriggerExecutionContext tec,CCTerm match,boolean checkblocked) {
		ReactivationContext rc = tec.getRC(match);
		if (rc == null)
			rc = tec.createRC(engine, match);
		if (!rc.isRegistered()) {
			rc.register(engine);
//			match.repStar.blockBindTrigger(rc);
		} else
			return false;//checkblocked;
		return false;
	}
	
	@Override
	public void match(CClosure engine,CCTerm[] regs,
			List<CCTrigger> path,int pathpos,TriggerExecutionContext tec,
			Deque<Object> candidates) {
		assert(tec != null);
		if (setReactivation(engine,tec,regs[m_EqRegNum],
				checkBlocked(path, pathpos))) {
			candidates.clear();
			return;
		}
		if (candidates.isEmpty()) {
			// No reactivation
			getCandidates(regs[m_EqRegNum], candidates, null, tec);
		}
		int size = next.getExpectedInputRegisterLength();
		UpdatableCongruenceBlocker blocker = tec.getBlocker();
		if (!candidates.isEmpty())
			blocker.update();
		while (!candidates.isEmpty()) {
			CCAppTerm candidate = (CCAppTerm)candidates.removeFirst();
			if (blocker.isBlocked(candidate))
				continue;
			blocker.block(candidate);
			CCTerm[] nextinput = produceOutput(regs, candidate, size);
			TriggerExecutionContext nextTec = tec.successor(nextinput, next);
			next.match(engine, nextinput, path, pathpos, nextTec,
					nextTec.getCandidates());
		}
		blocker.done();
	}
	@Override
	public int hashCode() {
		return m_EqRegNum + m_Symb * 13 + 
			Arrays.hashCode(m_RegCtl) * 1031;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof BindTrigger) {
			BindTrigger bt = (BindTrigger)obj;
			return bt.m_EqRegNum == m_EqRegNum && bt.m_Symb == m_Symb &&
				Arrays.equals(bt.m_RegCtl, m_RegCtl);
		}
		return false;
	}

	public final boolean isCandidate(CCTerm t,Set<CCAppTerm> matches) {
		if (t instanceof CCAppTerm) {
			CCAppTerm at = (CCAppTerm)t;
			if (at.func.parentPosition == m_Symb) {
				for (CCAppTerm at2 : matches) {
					if (at2.func.repStar == at.func.repStar &&
							at2.arg.repStar == at.arg.repStar)
						return false;
				}
				return true;
			}
		}
		return false;
	}
	public void getCandidates(CCTerm base, Deque<Object> candidates,
			CongruenceBlockerSet cbs, TriggerExecutionContext tec) {
		if (cbs == null)
			cbs = new CongruenceBlockerSet();
		UpdatableCongruenceBlocker ucb = tec.getBlocker();
		ucb.update();
		for (CCTerm t : base.repStar.members) {
			if (t instanceof CCAppTerm) {
				CCAppTerm at = (CCAppTerm)t;
				if (at.func.parentPosition == m_Symb) {
					if (!cbs.isBlocked(at) && !ucb.isBlocked(at)) {
						candidates.add(at);
						cbs.block(at);
					}
				}
			}
		}
		ucb.done();
	}

	@Override
	public String toString() {
		return "Bind " + m_EqRegNum + " " + m_Symb 
			+ " "+Arrays.toString(m_RegCtl);
	}

	@Override
	public int computeNumLiveRegisters() {
		int num = next.getExpectedInputRegisterLength();
		return m_EqRegNum > num ? m_EqRegNum + 1 : num;
	}

	@Override
	public boolean getsCandidates() {
		return true;
	}
}
