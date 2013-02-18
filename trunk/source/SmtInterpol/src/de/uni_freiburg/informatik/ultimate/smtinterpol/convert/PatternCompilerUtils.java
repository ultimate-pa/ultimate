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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.NonYieldTrigger;


/**
 * Utilities needed by a pattern compiler.
 * @author Juergen Christ
 */
public class PatternCompilerUtils {
	/**
	 * Helper class to create an instruction (insn) sequence in an arbitrary
	 * way.  You may append or prepend new instructions but the last instruction
	 * in the sequence has to be a Yield.
	 * @author Juergen Christ
	 */
	public static final class InsnSequence {
		private ArrayDeque<CCTrigger> m_sequence = new ArrayDeque<CCTrigger>();
		/**
		 * Append a trigger instruction to the sequence.
		 * @param trig Instruction to append.
		 */
		public void append(CCTrigger trig) {
			m_sequence.addLast(trig);
		}
		/**
		 * Prepend a trigger instruction to the sequence.
		 * @param trig Instruction to prepend.
		 */
		public void prepend(CCTrigger trig) {
			m_sequence.addFirst(trig);
		}
		/**
		 * Create a linked instruction sequence and return the correct 
		 * {@link TriggerData}.
		 * @param initregs Initial registers for this instruction sequence.
		 * @return TriggerData for this sequence.
		 */
		public TriggerData finish(CCTerm[] initregs) {
			Iterator<CCTrigger> it = m_sequence.descendingIterator();
			if (!it.hasNext())
				throw new RuntimeException(
						"Empty Trigger Instruction Sequence");
			CCTrigger trig = it.next();
			if (!(trig instanceof YieldTrigger))
				throw new RuntimeException(
						"Instruction Sequence not ending in a Yield Instruction!");
			while (it.hasNext()) {
				CCTrigger tmp = it.next();
				((NonYieldTrigger)tmp).setNext(trig);
				trig = tmp;
			}
			return new TriggerData(m_sequence.getFirst(),initregs,
					(YieldTrigger)m_sequence.getLast());
		}
		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (CCTrigger trig : m_sequence)
				sb.append(trig).append(", ");
			return sb.toString();
		}
	}
	private static void recursiveGetConstant(HashMap<Term, CCTerm> consts,
			Term t,ConvertFormula converter) {
		// I assume only universally bound variables in patterns
		if (t.getFreeVars().length == 0) {
			if (!consts.containsKey(t))
				consts.put(t, converter.convertTerm(t).toCCTerm());
		} else {
			assert(t instanceof ApplicationTerm);
			ApplicationTerm at = (ApplicationTerm)t;
			for (Term p : at.getParameters())
				recursiveGetConstant(consts, p, converter);
		}
	}
	/**
	 * Retrieve all constants appearing in <code>triggers</code>.
	 * @param triggers		The triggers.
	 * @param converter		The CNF-Converter
	 * @return All constants that appear in <code>triggers</code>.
	 */
	public static HashMap<Term,CCTerm> getConstants(Term[] triggers,
			ConvertFormula converter) {
		HashMap<Term, CCTerm> res = new HashMap<Term, CCTerm>();
		for (Term t : triggers)
			recursiveGetConstant(res, t, converter);
		return res;
	}
}
