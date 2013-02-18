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
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;


/**
 * A find instruction. For "malformed multitrigger" (e.g. f(x),g(y)), we have
 * "input" for find instructions as well. The input should contain all
 * substitutions discovered before:
 * 
 * Example:
 * <pre>
 * find f
 * find g
 * yield
 * </pre>
 * Here, we need to pass the substitution for <code>x</code> through the second
 * find instruction.
 * 
 * @author Juergen Christ
 */
public class FindTrigger extends Reverse0Trigger {
	
	private class FindReverse0Trigger extends Reverse0Trigger {

		public FindReverse0Trigger(int reverseNum) {
			super(reverseNum);
		}

		@Override
		protected int getNonReverse0InputLength() {
			return FindTrigger.this.m_nextNonRev0.
				getExpectedInputRegisterLength();
		}

		@Override
		protected CCTerm[] produceOutput(CCTerm[] regs, CCAppTerm match,
				int size, UpdatableCongruenceBlocker blocker) {
			return FindTrigger.this.produceOutput(regs, match, size, blocker);
		}
		
		public int hashCode() {
			return FindTrigger.this.hashCode();
		}
		public boolean equals(Object o) {
			if (o instanceof FindReverse0Trigger) {
				FindReverse0Trigger other = (FindReverse0Trigger)o;
				return m_reverseNum == other.m_reverseNum && 
					FindTrigger.this.equals(other.getFindTrigger());
			}
			return false;
		}
		FindTrigger getFindTrigger() {
			return FindTrigger.this;
		}

		@Override
		public int computeNumLiveRegisters() {
			return FindTrigger.this.getExpectedInputRegisterLength();
		}
		
		public String toString() {
			return "Find" + super.toString();
		}

		@Override
		protected UpdatableCongruenceBlocker getBlocker(
				TriggerExecutionContext tec) {
			while (tec.getTrigger() != FindTrigger.this)
				tec = tec.parent;
			return tec.getBlocker();
		}
	}

	CCBaseTerm m_Symb;
	int[] m_RegCtl;
	
	CCTrigger m_nextNonRev0;
	
	/**
	 * Create a find instruction.
	 * @param engine	CGraph management engine.
	 * @param symbol   Function symbol of the application to search.
	 * @param regCtl   Register control: {0: Function Symbol, 1-... Args}.
	 * 					-1 means "Drop the value"
	 */
	public FindTrigger(CClosure engine,FunctionSymbol symb,
			int[] regCtl) {
		this(engine,symb,regCtl,null);
	}
	
	/**
	 * Create a find instruction.
	 * @param engine	CGraph management engine.
	 * @param numRegs	Expected number of input registers.
	 * @param symbol   Function symbol of the application to search.
	 * @param regCtl   Register control: {0: Function Symbol, 1-... Args}.
	 * 					-1 means "Drop the value"
	 * @param next		The next instruction to execute after this bind.
	 */
	public FindTrigger(CClosure engine,FunctionSymbol symb,
			int[] regCtl,CCTrigger next) {
		super(symb.getParameterCount() - 1);
		assert regCtl.length == symb.getParameterCount() + 1 : 
			"Need register control for function symbol and all arguments";
		m_Symb = (CCBaseTerm)engine.getFuncTerm(symb);
		m_RegCtl = regCtl;
		int argsRemain = symb.getParameterCount() - 1;
		assert argsRemain >= 0 : "Find on constant";
		NonYieldTrigger set = this;
		for (int i = argsRemain; i >= 1;) {
			set.next = new FindReverse0Trigger(--i);
			set = (NonYieldTrigger)set.next;
		}
		m_nextNonRev0 = set.next = next;
	}
	
	protected CCTerm[] produceOutput(CCTerm[] input,CCAppTerm match,int size,
			UpdatableCongruenceBlocker congblocker) {
//		System.err.println("FindTrigger::produceOutput called with match " + match + " on regs " + Arrays.toString(input) + " RegCtl: " + Arrays.toString(m_RegCtl));
		assert(!match.isFunc);
		if (congblocker.isBlocked(match))
			return null;
		congblocker.block(match);
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
	
	// This gets (f x) for every n-ary f-currying
	@Override
	public void match(CClosure engine,CCTerm[] regs,List<CCTrigger> path,
			int pos,TriggerExecutionContext tec,Deque<Object> candidates) {
		if (candidates.isEmpty()) {
			if (setReactivation(engine,tec,m_Symb,m_Symb,checkBlocked(path,pos)))
				return;
			// We have to set the reactivation record such that we are notified
			// when new terms are created.
			for (Parent pa : m_Symb.repStar.ccpars.getParentInfo(0)) {
				if (!pa.isMarked())
					candidates.add(pa);
			}
		}
		HashSet<CCTerm> uniq = new HashSet<CCTerm>();
		if (m_reverseNum == 0) {
			int size = next.getExpectedInputRegisterLength();
			UpdatableCongruenceBlocker blocker = tec.getBlocker();
			if (!candidates.isEmpty())
				blocker.update();
			while (!candidates.isEmpty()) {
				Parent pac = (Parent) candidates.removeFirst();
				if (pac.isMarked())
					continue;
				CCAppTerm candidate = pac.getData();
				if (uniq.add(candidate.repStar)) return;
				CCTerm[] nextinput = produceOutput(regs, candidate, size,
						blocker);
				if (nextinput == null)
					continue;
				TriggerExecutionContext nextTec = tec.successor(nextinput,next);
				next.match(engine, nextinput, path, pos, nextTec,
						nextTec.getCandidates());
			}
			blocker.done();
		} else {
			assert(next instanceof Reverse0Trigger);
			TriggerExecutionContext nextTec = tec.successor(regs, next);
			while(!candidates.isEmpty()) {
				Parent pac = (Parent) candidates.removeFirst();
				if (pac.isMarked())
					continue;
				CCTerm candidate = pac.getData();
				for (Parent pa : candidate.repStar.ccpars.getParentInfo(0)) {
					if (!pa.isMarked())
						nextTec.addCandidate(pa);
				}
			}
			next.match(engine, regs, path, pos, nextTec, 
					nextTec.getCandidates());
		}
	}
	
	public int hashCode() {
		return m_Symb.hashCode() + 	Arrays.hashCode(m_RegCtl) * 1031;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof FindTrigger) {
			FindTrigger ft = (FindTrigger)obj;
			return ft.m_Symb == m_Symb && Arrays.equals(ft.m_RegCtl,m_RegCtl);
		}
		return false;
	}

	@Override
	public String toString() {
		return "Find " + m_Symb
			+ " "+Arrays.toString(m_RegCtl);
	}

	@Override
	public void setNext(CCTrigger next) {
		NonYieldTrigger set = this;
		while (set.next instanceof Reverse0Trigger)
			set = (NonYieldTrigger)set.next;
		set.next = next;
		m_nextNonRev0 = next;
	}

	@Override
	public int computeNumLiveRegisters() {
		return m_nextNonRev0.getExpectedInputRegisterLength();
	}

	@Override
	protected int getNonReverse0InputLength() {
		return m_nextNonRev0.getExpectedInputRegisterLength();
	}

	@Override
	public boolean getsCandidates() {
		return true;
	}

	@Override
	protected UpdatableCongruenceBlocker getBlocker(TriggerExecutionContext tec) {
		return tec.getBlocker();
	}

}
