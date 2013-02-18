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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext.ReactivationContext;


/**
 * A ReverseFind instruction (aka reverse or revfind).
 * @author Jochen Hoenicke, Juergen Christ
 */
public class ReverseTrigger extends NonYieldTrigger {
	
	private class ReverseReverse0Trigger extends Reverse0Trigger {

		public ReverseReverse0Trigger(int reverseNum) {
			super(reverseNum);
		}

		@Override
		protected int getNonReverse0InputLength() {
			return ReverseTrigger.this.m_nextNonRev0.
				getExpectedInputRegisterLength();
		}

		@Override
		protected CCTerm[] produceOutput(CCTerm[] regs, CCAppTerm match,
				int size, UpdatableCongruenceBlocker blocker) {
			return ReverseTrigger.this.produceOutput(regs, match, size, 
					blocker);
		}
		
		public int hashCode() {
			return ReverseTrigger.this.hashCode();
		}
		public boolean equals(Object o) {
			if (o instanceof ReverseReverse0Trigger) {
				ReverseReverse0Trigger other = (ReverseReverse0Trigger)o;
				return m_reverseNum == other.m_reverseNum &&
					ReverseTrigger.this.equals(other.getReverseTrigger());
			}
			return false;
		}
		ReverseTrigger getReverseTrigger() {
			return ReverseTrigger.this;
		}

		@Override
		public int computeNumLiveRegisters() {
			return ReverseTrigger.this.getExpectedInputRegisterLength();
		}
		
		public String toString() {
			return "Reverse" + super.toString();
		}

		@Override
		protected UpdatableCongruenceBlocker getBlocker(
				TriggerExecutionContext tec) {
			while (tec.getTrigger() != ReverseTrigger.this)
				tec = tec.parent;
			return tec.getBlocker();
		}

	}

	int m_ArgReg;
	int m_SymbArg;
	int m_ArgsLeft;
	int[] m_RegCtl;
	private CCTrigger m_nextNonRev0;
	
	/**
	 * Create a reverse instruction.
	 * @param engine	Congruence graph management.
	 * @param symb		Function symbol to search reverse.
	 * @param argnum	Number of the function argument (0-based).
	 * @param argReg	Register index containing the desired parameter 
	 * 					of the function application.
	 * @param regCtl   Register control: {0: Function Application, 1-... Args}.
	 * 					-1 means "Drop the value". Note that the "reverse
	 * 					argument" should not be specified.
	 * @param next		The next instruction to execute after this reverse.
	 */
	public ReverseTrigger(CClosure engine,FunctionSymbol symb,
			int argnum,int argReg,int[] regCtl,CCTrigger next) {
		super(next);
		assert(regCtl.length == symb.getParameterCount()) : 
			"Need Register control for Function application and all except one argument";
		m_ArgReg = argReg;
		m_SymbArg = engine.getFuncTerm(symb).parentPosition + argnum;
		m_ArgsLeft = symb.getParameterCount() - argnum - 1;
		m_RegCtl = regCtl;
		NonYieldTrigger set = this;
		for (int i = m_ArgsLeft; i >= 1;) {
			set.next = new ReverseReverse0Trigger(--i);
			set = (NonYieldTrigger)set.next;
		}
		m_nextNonRev0 = set.next = next;
	}
	// match is root of the currying
	private CCTerm[] produceOutput(CCTerm[] input,CCAppTerm match,int size,
			UpdatableCongruenceBlocker blocker) {
		if (blocker.isBlocked(match))
			return null;
		blocker.block(match);
		CCTerm[] output = Arrays.copyOf(input, size);
		assert(!match.isFunc);
		CCAppTerm cur = match;
		// Now, cur is the application we want
		if (m_RegCtl[0] != -1)
			output[m_RegCtl[0]] = cur;
		for (int i = m_RegCtl.length - 1; i > 1; --i) {
			if (cur.arg == match)
				cur = (CCAppTerm)cur.func;
			int ctl = m_RegCtl[i];
			if (ctl != -1) {
				output[ctl] = cur.arg;
			}
			cur = (CCAppTerm)cur.func;
		}
		// Prevent ClassCastException in the loop above
		if (m_RegCtl[1] != -1) {
			if (cur.arg == match)
				cur = (CCAppTerm)cur.func;
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
			CCParentInfo pa = match.repStar.ccpars.createInfo(m_SymbArg);
//			pa.addReverseTrigger(rc);
		} else
			return false;//checkblocked;
		return false;
	}
	
//	private void singleMatch(CClosure engine,List<CCTrigger> path,int pathpos,
//			CCTerm[] regs,CCAppTerm match,TriggerExecutionContext tec,
//			boolean checkblocked) {
//		if (m_ArgsLeft == 0) {
//			int size = next.getExpectedInputRegisterLength();
//			CCTerm[] nextinput = produceOutput(regs, match, size);
//			TriggerExecutionContext nextTec =
//				tec.successor(nextinput, next);
//			next.match(engine,nextinput,path,pathpos,nextTec,nextTec.candidates);
//		} else {
//			TriggerExecutionContext nextTec = tec.successor(regs, next);
//			for (Parent pa : match.repStar.ccpars.getParentInfo(0)) {
//				if (!pa.isMarked()) {
//					CCAppTerm candidate = pa.getData();
//					if (setReactivation(
//							engine,tec,candidate.func,checkblocked))
//						continue;
//					nextTec.candidates.add(candidate);
//				}
//			}
//			next.match(engine,regs,path,pathpos,nextTec,nextTec.candidates);
//		}
//	}
	
	private void getCandidates(CCTerm base,Deque<Object> newcandidates) {
		for (Parent pa : base.repStar.ccpars.getParentInfo(m_SymbArg)) {
			if (!pa.isMarked()) {
				newcandidates.add(pa);
			}
		}
	}
	
	@Override
	public void match(CClosure engine,CCTerm[] regs,List<CCTrigger> path,
			int pos,TriggerExecutionContext tec,Deque<Object> candidates) {
		if (setReactivation(engine,tec,regs[m_ArgReg],
				checkBlocked(path, pos))) {
			candidates.clear();
			return;
		}
		if (candidates.isEmpty()) {
			// No reactivation
			getCandidates(regs[m_ArgReg], candidates);
		}
		if (m_ArgsLeft != 0) {
			assert(next instanceof Reverse0Trigger);
			TriggerExecutionContext nextTec = tec.successor(regs, next);
			while (!candidates.isEmpty()) {
				Parent pac = (Parent) candidates.removeFirst();
				if (pac.isMarked())
					continue;
				CCTerm candidate = pac.getData();
				for (Parent pa : candidate.repStar.ccpars.getParentInfo(0))
					nextTec.addCandidate(pa);
			}
			next.match(engine, regs, path, pos, nextTec, 
					nextTec.getCandidates());
		} else {
			int size = next.getExpectedInputRegisterLength();
			UpdatableCongruenceBlocker blocker = tec.getBlocker();
			if (!candidates.isEmpty())
				blocker.update();
			while (!candidates.isEmpty()) {
				Parent pac = (Parent) candidates.removeFirst();
				CCTerm candidate = pac.getData();
				CCTerm[] newregs = produceOutput(regs,(CCAppTerm)candidate,size,
						blocker);
				if (newregs == null)
					continue;
				TriggerExecutionContext nextTec = tec.successor(newregs, next);
				next.match(engine, newregs, path, pos, nextTec,
						nextTec.getCandidates());
			}
			blocker.done();
		}
	}
	
	@Override
	public int hashCode() {
		return m_ArgReg + m_SymbArg * 13 + Arrays.hashCode(m_RegCtl) * 1031;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof ReverseTrigger) {
			ReverseTrigger rt = (ReverseTrigger)obj;
			return rt.m_ArgReg == m_ArgReg && rt.m_SymbArg == m_SymbArg &&
				Arrays.equals(rt.m_RegCtl,m_RegCtl);
		}
		return false;
	}

	@Override
	public String toString() {
		return "Reverse " + m_ArgReg + " "  + m_SymbArg 
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
		int num = m_nextNonRev0.getExpectedInputRegisterLength();
		if (m_ArgReg >= num)
			num = m_ArgReg + 1;
		return num;
	}
	@Override
	public boolean getsCandidates() {
		return true;
	}
}
