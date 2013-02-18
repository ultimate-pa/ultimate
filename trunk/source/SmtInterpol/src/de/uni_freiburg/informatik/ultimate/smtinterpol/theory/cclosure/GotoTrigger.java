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

import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

public class GotoTrigger extends CCTrigger {

	private List<CCTrigger> m_Succs;
	
	public GotoTrigger(CCTrigger t1,CCTrigger t2) {
		super();
		m_Succs = new ArrayList<CCTrigger>();
		m_Succs.add(t1);
		m_Succs.add(t2);
		numRegs = t1.getExpectedInputRegisterLength();
		int tmp = t2.getExpectedInputRegisterLength();
		if (tmp > numRegs)
			numRegs = tmp;
	}
	
	@Override
	public void match(CClosure engine,CCTerm[] regs,List<CCTrigger> path,
			int pos,TriggerExecutionContext tec,Deque<Object> unused) {
		assert(tec != null);
		if (path != null) {
			// We consumed the choice...
			CCTrigger next = path.get(pos);
			TriggerExecutionContext nextTec =
				tec.successor(regs, next);
			next.match(engine, regs, path, pos + 1, nextTec,
					nextTec.getCandidates());
		} else {
			for (CCTrigger t : m_Succs) {
				TriggerExecutionContext nextTec =
					tec.successor(regs, t);
				t.match(engine, regs, null, 0, nextTec,
						nextTec.getCandidates());
			}
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof GotoTrigger) {
			return ((GotoTrigger)obj).m_Succs.equals(m_Succs);
		}
		return false;
	}

	public CCTrigger add(CCTrigger trig) {
		int tmp = trig.getExpectedInputRegisterLength();
		if (tmp > numRegs)
			numRegs = tmp;
		for (CCTrigger t : m_Succs) {
			if (t.equals(trig))
				return t;
		}
		m_Succs.add(trig);
		return trig;
	}
	
	public CCTrigger find(CCTrigger trig) {
		for (CCTrigger t : m_Succs)
			if (t.equals(trig))
				return t;
		throw new InternalError("Searching non-existant!");
//		return null;
	}
	
	public int remove(CCTrigger trig) {
		for (Iterator<CCTrigger> it = m_Succs.iterator(); it.hasNext(); ) {
			if (it.next().equals(trig)) {
				if (numRegs == trig.getExpectedInputRegisterLength())
					numRegs = -1;
				it.remove();
				return m_Succs.size();
			}
		}
		throw new InternalError("Removing non-existent!");
//		return m_Succs.size();
	}
	
	public CCTrigger getSingleElement() {
		assert(m_Succs.size() == 1);
		return m_Succs.iterator().next();
	}
	
	@Override
	public int getExpectedInputRegisterLength() {
		if (numRegs == -1) {
			for (CCTrigger t : m_Succs) {
				int tmp = t.getExpectedInputRegisterLength();
				if (numRegs < tmp)
					numRegs = tmp;
			}
		}
		return numRegs;
	}

	@Override
	public int hashCode() {
		return m_Succs.hashCode();
	}

	@Override
	public CCTrigger next() {
		throw new InternalError("next on GotoTrigger???");
	}

	@Override
	public int computeNumLiveRegisters() {
		throw new InternalError("Should not be called on GotoTrigger!");
	}

	@Override
	public boolean getsCandidates() {
		return false;
	}

}
