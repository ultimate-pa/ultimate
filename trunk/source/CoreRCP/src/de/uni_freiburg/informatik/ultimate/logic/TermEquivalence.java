/*
 * Copyright (C) 2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class TermEquivalence extends NonRecursive{
	
	private ScopedHashMap<TermVariable, TermVariable> m_Renaming =
			new ScopedHashMap<TermVariable, TermVariable>();
	
	private void beginScope() {
		m_Renaming.beginScope();
	}
	
	private void endScope() {
		m_Renaming.endScope();
	}
	
	private void addRenaming (TermVariable lvar, TermVariable rvar) {
		m_Renaming.put(lvar, rvar);
	}
	
	private boolean checkRenaming(TermVariable lvar, TermVariable rvar) {
		return m_Renaming.get(lvar) == rvar;
	}
	
	@SuppressWarnings("serial")
	private static final class NotEq extends RuntimeException {}
	
	private final static class EndScope implements Walker {
		public final static EndScope INSTANCE = new EndScope();
		@Override
		public void walk(NonRecursive engine) {
			TermEquivalence te = (TermEquivalence) engine;
			te.endScope();
		}
	}
	
	private final static class AddRenaming implements Walker {
		private final TermVariable m_lvar, m_rvar;
		public AddRenaming(TermVariable lvar, TermVariable rvar) {
			m_lvar = lvar;
			m_rvar = rvar;
		}
		@Override
		public void walk(NonRecursive engine) {
			TermEquivalence te = (TermEquivalence) engine;
			te.addRenaming(m_lvar, m_rvar);
		}
	}
		
	
	private final static class TermEq implements Walker {

		private Term m_lhs, m_rhs;
		
		public TermEq(Term lhs, Term rhs) {
			m_lhs = lhs;
			m_rhs = rhs;
		}
		
		private final void notEqual() {
			throw new NotEq();
		}
		
		@Override
		public void walk(NonRecursive engine) {
			TermEquivalence te = (TermEquivalence) engine;
			if (m_lhs != m_rhs) {
				if (m_lhs.getClass() != m_rhs.getClass())
					// Cannot be equal
					notEqual();
				if (m_lhs instanceof ApplicationTerm) {
					ApplicationTerm l = (ApplicationTerm) m_lhs;
					ApplicationTerm r = (ApplicationTerm) m_rhs;
					if (l.getFunction() != r.getFunction())
						notEqual();
					Term[] lparams = l.getParameters();
					Term[] rparams = r.getParameters();
					if (lparams.length != rparams.length)
						notEqual();
					for (int i = 0; i < lparams.length; ++i)
						te.enqueueWalker(new TermEq(lparams[i], rparams[i]));
				} else if (m_lhs instanceof AnnotatedTerm) {
					AnnotatedTerm l = (AnnotatedTerm) m_lhs;
					AnnotatedTerm r = (AnnotatedTerm) m_rhs;
					Annotation[] lannot = l.getAnnotations();
					Annotation[] rannot = r.getAnnotations();
					if (rannot.length != lannot.length)
						notEqual();
					for (int i = 0; i < lannot.length; ++i) {
						if (!lannot[i].getKey().equals(rannot[i].getKey()))
							notEqual();
						if (lannot[i].getValue() instanceof Term &&
								rannot[i].getValue() instanceof Term)
							te.enqueueWalker(new TermEq(
									(Term) lannot[i].getValue(),
									(Term) rannot[i].getValue()));
						else if (lannot[i].getValue() instanceof Term[] &&
								rannot[i].getValue() instanceof Term[]) {
							Term[] lv = (Term[]) lannot[i].getValue();
							Term[] rv = (Term[]) lannot[i].getValue();
							if (lv.length != rv.length)
								notEqual();
							for (int j = 0; j < lv.length; ++j)
								te.enqueueWalker(new TermEq(lv[j], rv[j]));
						} else if (! lannot[i].getValue().equals(
								rannot[i].getValue()))
							notEqual();
					}
				} else if (m_lhs instanceof LetTerm) {
					LetTerm llet = (LetTerm) m_lhs;
					LetTerm rlet = (LetTerm) m_rhs;
					TermVariable[] lvars = llet.getVariables();
					TermVariable[] rvars = rlet.getVariables();
					if (lvars.length != rvars.length)
						notEqual();
					te.enqueueWalker(EndScope.INSTANCE);
					te.enqueueWalker(
							new TermEq(llet.getSubTerm(), rlet.getSubTerm()));
					Term[] lvals = llet.getValues();
					Term[] rvals = rlet.getValues();
					for (int i = 0; i < lvars.length; ++i) {
						te.enqueueWalker(new AddRenaming(lvars[i], rvars[i]));
						te.enqueueWalker(new TermEq(lvals[i], rvals[i]));
					}
//					te.enqueueWalker(BeginScope.INSTANCE);
					te.beginScope();
				} else if (m_lhs instanceof QuantifiedFormula) {
					QuantifiedFormula lq = (QuantifiedFormula) m_lhs;
					QuantifiedFormula rq = (QuantifiedFormula) m_rhs;
					if (lq.getQuantifier() != rq.getQuantifier())
						notEqual();
					TermVariable[] lv = lq.getVariables();
					TermVariable[] rv = rq.getVariables();
					if (lv.length != rv.length)
						notEqual();
					te.enqueueWalker(EndScope.INSTANCE);
					te.beginScope();
					for (int i = 0; i < lv.length; ++i)
						if (lv[i] != rv[i]) {
							if (lv[i].getSort() != rv[i].getSort())
								notEqual();
							te.addRenaming(lv[i], rv[i]);
						}
					te.enqueueWalker(
							new TermEq(lq.getSubformula(), rq.getSubformula()));
				} else if (m_lhs instanceof TermVariable) {
					TermVariable lv = (TermVariable) m_lhs;
					TermVariable rv = (TermVariable) m_rhs;
					if (!te.checkRenaming(lv, rv))
						notEqual();
				}// Term case switch
			}
		}
	}
	
	public boolean equal(Term lhs, Term rhs) {
		try {
			run(new TermEq(lhs, rhs));
			return true;
		} catch (NotEq ignored) {
			reset();
			return false;
		}
	}
	
}
