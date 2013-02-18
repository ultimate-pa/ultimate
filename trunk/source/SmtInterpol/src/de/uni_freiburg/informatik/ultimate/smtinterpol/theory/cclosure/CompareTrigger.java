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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermPairHash.Info;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext.ReactivationContext;


// TODO Do not register multiple times for the same merge and input registers
/**
 * A compare instruction.
 * @author Jochen Hoenicke, Juergen Christ
 */
public class CompareTrigger extends NonYieldTrigger {

	int m_RegNum1;
	int m_RegNum2;
	/**
	 * Create a compare instruction to check whether the content of two
	 * registers is in the same equivalence class.
	 * @param regNum1 	Index of the first register to compare.
	 * @param regNum2 	Index of the second register to compare.
	 */
	public CompareTrigger(int regNum1,int regNum2) {
		this(regNum1,regNum2,null);
	}
	/**
	 * Create a compare instruction to check whether the content of two
	 * registers is in the same equivalence class.
	 * @param regNum1 	Index of the first register to compare.
	 * @param regNum2 	Index of the second register to compare.
	 * @param next		Next instruction in the sequence.
	 */
	public CompareTrigger(int regNum1,int regNum2,CCTrigger next) {
		super(next);
		m_RegNum1 = regNum1;
		m_RegNum2 = regNum2;
	}
	
	@Override
	public void match(CClosure engine,CCTerm[] regs,List<CCTrigger> path,
			int pos,TriggerExecutionContext tec,Deque<Object> unused) {
		assert(tec != null);
		if (regs[m_RegNum1].repStar == regs[m_RegNum2].repStar) {
			TriggerExecutionContext nextTec = tec.successor(regs, next);
			next.match(engine,regs,path,pos,nextTec,nextTec.getCandidates());
		} else {
			// Do the reactivation
			/*
			 * XXX Check whether this hack works.  We cannot create the
			 * reactivation context for regs[m_RegNum1].repStar since that might
			 * change and we might block the same TEC multiple times on the same
			 * equivalence class.
			 * 
			 * For now, I try to fix this by giving regs[m_RegNum1] as match.
			 * This ensures that we get the same ReactivationContext on
			 * successive calls to match.
			 */
			ReactivationContext nrc = tec.getRC(regs[m_RegNum1]);
			if (nrc == null)
				nrc = tec.createRC(engine, regs[m_RegNum1]);
			if (!nrc.isRegistered()) {
				Info info = engine.pairHash.getInfo(regs[m_RegNum1].repStar, 
						regs[m_RegNum2].repStar);
				if (info == null) {
					info = new CCTermPairHash.Info(regs[m_RegNum1].repStar, 
							regs[m_RegNum2].repStar);
					engine.pairHash.add(info);
				}
//				info.blockCompareTrigger(nrc);
			}
		}
	}
	@Override
	public int hashCode() {
		return m_RegNum1 + m_RegNum2 * 1031;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CompareTrigger) {
			CompareTrigger ct = (CompareTrigger)obj;
			return ct.m_RegNum1 == m_RegNum1 && ct.m_RegNum2 == m_RegNum2;
		}
		return false;
	}
	@Override
	public String toString() {
		return "Compare " + m_RegNum1 + " " + m_RegNum2;
	}
	@Override
	public int computeNumLiveRegisters() {
		int num = next.getExpectedInputRegisterLength();
		if (m_RegNum1 >= num)
			num = m_RegNum1 + 1;
		if (m_RegNum2 >= num)
			num = m_RegNum2 + 1;
		return num;
	}
	@Override
	public boolean getsCandidates() {
		return false;
	}
}
