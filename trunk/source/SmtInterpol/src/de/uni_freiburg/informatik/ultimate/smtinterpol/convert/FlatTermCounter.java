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
import java.util.Deque;
import java.util.HashMap;

public class FlatTermCounter {
	private HashMap<FlatTerm, Integer> m_Counts =
		new HashMap<FlatTerm, Integer>();
	private Deque<FlatTerm> m_Todo = new ArrayDeque<FlatTerm>();
	private boolean m_CountNonBooleanOnly;
	
	public FlatTermCounter(boolean countNonBooleanOnly) {
		m_CountNonBooleanOnly = countNonBooleanOnly;
	}
	
	public boolean isUnique(FlatTerm term) {
		Integer count = m_Counts.get(term);
		assert count != null;
		return count == 1;
	}
	
	public void decreaseCount(FlatTerm term) {
		Integer count = m_Counts.get(term);
		assert count != null;
		if (count == 1)
			m_Counts.remove(term);
		else
			m_Counts.put(term, count - 1);
	}
	
	public void addToCount(FlatTerm term, int add) {
		Integer count = m_Counts.get(term);
		if (count == null)
			m_Counts.put(term, add);
		else {
			int newcount = count + add;
			if (newcount == 0)
				m_Counts.remove(term);
			else
				m_Counts.put(term, newcount);
		}
	}

	public void reset() {
		// We should be done before this is called!
		assert m_Todo.isEmpty();
		m_Counts.clear();
	}

	public void count(FlatTerm t) {
		m_Todo.add(t);
		run();
	}
	
	private void run() {
		while (!m_Todo.isEmpty()) {
			FlatTerm t = m_Todo.removeLast();
			if (m_CountNonBooleanOnly && t instanceof FlatFormula)
				enqueueChildren(t);
			else {
				Integer count = m_Counts.get(t);
				if (count != null)
					m_Counts.put(t, count + 1);
				else {
					m_Counts.put(t, 1);
					enqueueChildren(t);
				}
			}
		}
	}
	
	private void enqueueChildren(FlatTerm t) {
		// Special treatment to simplify code
		if (t instanceof DivideTerm)
			t = ((DivideTerm) t).m_affineTerm;
		else if (t instanceof LeqZeroFormula)
			t = ((LeqZeroFormula) t).mTerm;
		else if (t instanceof EqualityFormula.NegatedFormula)
			t = ((EqualityFormula.NegatedFormula) t).negate();
		else if (t instanceof LeqZeroFormula.NegatedFormula)
			t = ((LeqZeroFormula)((LeqZeroFormula.NegatedFormula) t).negate()).
				mTerm;
		else if (t instanceof NegClauseFormula)
			t = ((NegClauseFormula) t).negate();
		else if (t instanceof NegForallFormula)
			t = ((NegForallFormula) t).negate();
		else if (t instanceof SharedAffineTerm)
			t = ((SharedAffineTerm) t).m_affineTerm;
		
		// Now, we have some general cases
		if (t instanceof AffineTerm) {
			AffineTerm at = (AffineTerm) t;
			m_Todo.addAll(at.getSummands().keySet());
		} else if (t instanceof FlatApplicationTerm) {
			FlatApplicationTerm fat = (FlatApplicationTerm) t;
			for (FlatTerm p : fat.getParameters())
				m_Todo.add(p);
		} else if (t instanceof ClauseFormula) {
			m_Todo.addAll(((ClauseFormula) t).getSubFormulas());
		} else if (t instanceof EqualityFormula) {
			EqualityFormula ef = (EqualityFormula) t;
			m_Todo.add(ef.mLhs);
			m_Todo.add(ef.mRhs);
		} else if (t instanceof ForallFormula) {
			// TODO
		} else if (t instanceof IfThenElseFormula) {
			IfThenElseFormula itef = (IfThenElseFormula) t;
			m_Todo.add(itef.cond);
			m_Todo.add(itef.thenForm);
			m_Todo.add(itef.elseForm);
		} else if (t instanceof IfThenElseTerm) {
			IfThenElseTerm itet = (IfThenElseTerm) t;
			m_Todo.add(itet.mCond);
			m_Todo.add(itet.mThen);
			m_Todo.add(itet.mElse);
		}
	}	
	
	public String toString() {
		return m_Counts.toString();
	}
}
