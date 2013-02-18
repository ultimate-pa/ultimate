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

/**
 * Class to lift term ITEs as close to Boolean level as possible.  This should
 * yield better performance since the theory solvers cannot reason about these
 * kinds of things.
 * @author Juergen Christ
 */
public class Lifter {
	
	private static class Task {
		private FlatTerm m_Parent;
		private FlatTerm m_Term;
		private boolean m_Expand;
		public Task(FlatTerm parent, FlatTerm term, boolean expand) {
			m_Parent= parent;
			m_Term = term;
			m_Expand = expand;
		}
		public FlatTerm getParent() {
			return m_Parent;
		}
		public FlatTerm getTerm() {
			return m_Term;
		}
		public boolean isExpand() {
			return m_Expand;
		}
		public void switchToCollect() {
			m_Expand = false;
		}
	}
	
	private ConvertFormula m_Converter;
	private FlatTermCounter m_Counter;
	private ArrayDeque<Task> m_Todo = new ArrayDeque<Task>();
	private HashMap<FlatTerm, FlatTerm> m_Transformed =
		new HashMap<FlatTerm, FlatTerm>();
	
	/**
	 * Ctor.
	 * @param converter The converter to use.
	 */
	public Lifter(ConvertFormula converter) {
		m_Converter = converter;
	}
	
	public void setCounter(FlatTermCounter counter) {
		m_Counter = counter;
	}
	
	public FlatFormula lift(FlatFormula ff) {
		m_Todo.add(new Task(null, ff, true));
		run();
		return (FlatFormula) m_Transformed.get(ff);
	}
	
	private void run() {
		while (!m_Todo.isEmpty()) {
			Task task = m_Todo.removeLast();
			// Only transform once
			if (!m_Transformed.containsKey(task.getTerm())) {
				if (task.isExpand()) {
					FlatTerm term = task.getTerm();
					if (isLiftingCandidate(task))
//						lift((IfThenElseTerm) term, task.getParent());
					task.switchToCollect();
					m_Todo.add(task);
					enqueueChildren(term);
				} else {
//					collect(task.getTerm());
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
		
		if (t instanceof AffineTerm) {
			AffineTerm at = (AffineTerm) t;
			for (FlatTerm sub : at.getSummands().keySet())
				m_Todo.add(new Task(at, sub, true));
		} else if (t instanceof FlatApplicationTerm) {
			FlatApplicationTerm fat = (FlatApplicationTerm) t;
			for (FlatTerm p : fat.getParameters())
				m_Todo.add(new Task(fat, p, true));
		} else if (t instanceof ClauseFormula) {
			for (FlatTerm sub : ((ClauseFormula) t).getSubFormulas())
				m_Todo.add(new Task(t, sub, true));
		} else if (t instanceof EqualityFormula) {
			EqualityFormula ef = (EqualityFormula) t;
			m_Todo.add(new Task(ef, ef.mLhs, true));
			m_Todo.add(new Task(ef, ef.mRhs, true));
		} else if (t instanceof ForallFormula) {
			// TODO
		} else if (t instanceof IfThenElseFormula) {
			IfThenElseFormula itef = (IfThenElseFormula) t;
			m_Todo.add(new Task(t, itef.cond, true));
			m_Todo.add(new Task(t, itef.thenForm, true));
			m_Todo.add(new Task(t, itef.elseForm, true));
		} else if (t instanceof IfThenElseTerm) {
			IfThenElseTerm itet = (IfThenElseTerm) t;
			m_Todo.add(new Task(t, itet.mCond, true));
			m_Todo.add(new Task(t, itet.mThen, true));
			m_Todo.add(new Task(t, itet.mElse, true));
		}
	}
	
	private boolean isLiftingCandidate(Task task) {
		return task.getTerm() instanceof IfThenElseTerm &&
			m_Counter.isUnique(task.getTerm());
	}

}
