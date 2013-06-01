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

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.util.UnifyHash;


/**
 * Store a trigger instruction for later processing. Every TEC contains a stack
 * level and an undo information. Once the merge stack in the cclosure is
 * backtracked below the stack depth, the undo information is used to remove
 * the trigger contained in this TEC from the internal structure.
 * @author Juergen Christ
 */
public class TriggerExecutionContext {
	public class ReactivationContext 
	extends SimpleListable<ReactivationContext> {
		private int m_stackdepth;
		private CCTerm m_match;
		ReactivationContext prevRC;
		public ReactivationContext() {
			m_stackdepth = 0;
			m_match = null;
		}
		public ReactivationContext(int stackdepth,CCTerm match) {
			m_stackdepth = stackdepth;
			m_match = match;
		}
		public int hashCode() {
			return m_match.hashCode();
		}
		public boolean equals(Object o) {
			if (o instanceof ReactivationContext) {
				ReactivationContext other = (ReactivationContext)o;
				return other.m_match == m_match;
			}
			return m_match == o;
		}
		public String toString() {
			return TriggerExecutionContext.this.toString() + " with match " + 
				m_match;
		}
		public int getStackdepth() {
			return m_stackdepth;
		}
		public TriggerExecutionContext getTEC() {
			return TriggerExecutionContext.this;
		}
		public void undo() {
			if (inList()) {
				removeFromList();
				// XXX Check this: Does this only clear invalid instances???
				if (getTrigger().getsCandidates())
					getTEC().candidates.clear();
				if (m_match instanceof CCAppTerm)
					getTEC().getBlocker().remove((CCAppTerm)m_match);
			}
		}
		public boolean isRegistered() {
			return inList();
		}
		public void register(CClosure engine) {
//			System.err.println("Registering " + this);
			m_stackdepth = engine.getStackDepth();
		}
		public CCTerm getMatch() {
			return m_match;
		}
		public int getStackDepth() {
			return m_stackdepth;
		}
	}
	
	private static UnifyHash<CCTerm[]> g_RegUnifier;
	private static CCTerm[] unifyRegs(CCTerm[] regs) {
		int hash = Arrays.hashCode(regs);
		if (g_RegUnifier == null) {
			g_RegUnifier = new UnifyHash<CCTerm[]>();
			g_RegUnifier.put(hash, regs);
			return regs;
		}
		for (CCTerm[] it : g_RegUnifier.iterateHashCode(hash)) {
			if (Arrays.equals(it, regs)) {
				return it;
			}
		}
		g_RegUnifier.put(hash, regs);
		return regs;
	}
	CCTerm[] m_inputRegs;
	CCTrigger m_trig;
	// Lazily initialized successor set
	UnifyHash<TriggerExecutionContext> succset;
	// Lazily initialized reactivation context set;
	RCSet rcset;
	private Deque<Object> candidates;
	boolean passive;
	TriggerExecutionContext parent;
	TriggerExecutionContext next,prev;
	int stacksize;
	UpdatableCongruenceBlocker congblocker;
	
	TriggerExecutionContext() {
		next = prev = this;
	}

	public TriggerExecutionContext(TriggerExecutionContext parent,
			CCTerm[] inputRegs, CCTrigger trig) {
		assert parent != null : "Wrong backward chain!";
		assert trig != null : "Trigger instruction must be given!";
		this.parent = parent;
		m_inputRegs = unifyRegs(inputRegs);
		m_trig = trig;
		if (trig.getsCandidates())
			candidates = new ArrayDeque<Object>();
	}
	public CCTerm[] getRegisters() {
		return m_inputRegs;
	}
	public int hashCode() {
		return hash(m_inputRegs, m_trig);
	}
	public boolean equals(Object o) {
		if (o instanceof TriggerExecutionContext) {
			TriggerExecutionContext tec = (TriggerExecutionContext)o;
			return Arrays.equals(tec.m_inputRegs,m_inputRegs) &&
				tec.m_trig == m_trig;
		}
		return false;
	}
	public boolean equals(CCTerm[] regs,CCTrigger trig) {
		return m_trig == trig && Arrays.equals(m_inputRegs, regs);
	}
	public final CCTrigger getTrigger() {
		return m_trig;
	}
	public String toString() {
		return m_trig.toString() + " on " + Arrays.toString(m_inputRegs);
	}
	public TriggerExecutionContext successor(CCTerm[] regs,CCTrigger trig) {
		TriggerExecutionContext succ = null;
		int hash = hash(regs, trig);
		if (succset == null)
			succset = new UnifyHash<TriggerExecutionContext>();
		else {
			for (TriggerExecutionContext tec : succset.iterateHashCode(hash)) {
				if (tec.equals(regs, trig)) {
					succ = tec;
					break;
				}
			}
		}
		if (succ == null) {
			succ = new TriggerExecutionContext(this,regs,trig);
			succset.put(hash,succ);
		}
		return succ;
	}
	public ReactivationContext getRC(CCTerm match) {
		return rcset == null ? null : rcset.get(match);
	}
	public ReactivationContext createRC(CClosure engine,CCTerm match) {
		assert(getRC(match) == null);
		if (rcset == null)
			rcset = new RCSet();
		ReactivationContext res = 
			new ReactivationContext(engine.getStackDepth(),match);
//		System.err.println("Registering " + res + " for Literal " + engine.lastLit);
		rcset.add(res);
//		engine.appendRC(res);
		return res;
	}
	
	public static int hash(CCTerm[] regs,CCTrigger trig) {
		return Arrays.hashCode(regs) + 1031 * trig.hashCode();
	}
	public void reexecute(CClosure engine) {
		m_trig.match(engine,m_inputRegs,null,0,this,candidates);
	}
	public boolean isPassive() {
		return passive;
	}
	public void passivate() {
		passive = true;
	}
	public void addCandidate(Object candidate) {
		if (!candidates.contains(candidate))
			candidates.add(candidate);
	}
	public void addAllCandidates(Set<Object> newcandidates) {
		candidates.addAll(newcandidates);
	}
	public Deque<Object> getCandidates() {
		return candidates;
	}
	void addSuccessor(TriggerExecutionContext tmp) {
		if (succset == null)
			succset = new UnifyHash<TriggerExecutionContext>();
		succset.put(tmp.hashCode(), tmp);
	}
	UpdatableCongruenceBlocker getBlocker() {
		if (congblocker == null)
			congblocker = new UpdatableCongruenceBlocker();
		return congblocker;
	}
	public boolean scheduledForReexecution() {
		return !candidates.isEmpty();
	}
}
