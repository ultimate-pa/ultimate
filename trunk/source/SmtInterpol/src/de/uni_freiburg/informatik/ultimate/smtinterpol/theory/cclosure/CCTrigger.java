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

/**
 * Representation of a trigger command.
 * @author Jochen Hoenicke, Juergen Christ
 */
public abstract class CCTrigger {
	// Expected input length of the register array
	protected int numRegs;
	protected CCTrigger() {
		numRegs = -1;
	}
	public int getExpectedInputRegisterLength() {
		if (numRegs == -1) {
			numRegs = computeNumLiveRegisters();
		}
		return numRegs;
	}
	/**
	 * Try to match this trigger against a given term w.r.t. some registers.
	 * @param engine		EGraph management engine.
	 * @param regs			Registers to operate on.
	 * @param path	 		Insertion path to descend when this instruction
	 * 						sequence is executed directly after insertion into a
	 * 						trigger tree.
	 * @param pathpos		Position of the next instruction to execute in the
	 * 						insertion path.
	 * @param tec			Context for this "trigger/register state".
	 * @param rc			Context for the reactivation.
	 * @param hint			Hint for this instruction.
	 */
	public abstract void match(CClosure engine,CCTerm[] regs,
			List<CCTrigger> path,int pathpos,TriggerExecutionContext tec,
			Deque<Object> candidates);
	public abstract CCTrigger next();
	public abstract int computeNumLiveRegisters();
	protected boolean checkBlocked(List<CCTrigger> path,int pathpos) {
		return path == null || path.size() == pathpos;
	}
	public abstract boolean getsCandidates();
}
