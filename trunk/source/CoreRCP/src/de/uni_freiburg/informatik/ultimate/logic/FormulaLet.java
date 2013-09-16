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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class FormulaLet extends NonRecursive {
	private ArrayDeque<Map<Term, TermInfo>> m_Visited;
	private ArrayDeque<Term> m_ResultStack;
	private int m_CseNum;
	private LetFilter m_Filter = null;
	
	public static interface LetFilter {
		public boolean isLettable(Term t);
	}
	
	public FormulaLet() {
	}

	public FormulaLet(LetFilter filter) {
		this.m_Filter = filter;
	}
	
	public Term let(Term input) {
		input = new FormulaUnLet().unlet(input);
		m_CseNum = 0;
		m_Visited = new ArrayDeque<Map<Term,TermInfo>>();
		m_ResultStack = new ArrayDeque<Term>();
		run(new Letter(input));
		Term result = m_ResultStack.removeLast();
		assert m_ResultStack.size() == 0 && m_Visited.size() == 0;
		assert new TermEquivalence().equal(
				new FormulaUnLet().unlet(result), input);
		m_ResultStack = null;
		m_Visited = null;
		return result;
	}
	
	static class Letter implements Walker {
		Term m_Term;
		public Letter(Term term) {
			m_Term = term;
		}
		
		public void walk(NonRecursive engine) {
			if (m_Term instanceof TermVariable
				|| m_Term instanceof ConstantTerm) {
				((FormulaLet) engine).m_ResultStack.addLast(m_Term);
				return;
			}
			((FormulaLet) engine).m_Visited.addLast(new HashMap<Term, FormulaLet.TermInfo>());
			TermInfo info = new TermInfo(m_Term);
			((FormulaLet) engine).m_Visited.getLast().put(m_Term, info);
			engine.enqueueWalker(new Walker() {
				public void walk(NonRecursive engine) {
					((FormulaLet) engine).m_Visited.removeLast();
				}
			});
			engine.enqueueWalker(new Transformer(info, true));
			engine.enqueueWalker(info);
		}
	}
	
	private final static class TermInfo extends TermWalker {
		int                 m_Count;
		int                 m_Seen;
		ArrayList<TermInfo> m_LettedTerms;
		TermVariable        m_Subst;
		TermInfo            m_Parent;
		int                 m_pDepth;
		public TermInfo(Term term) {
			super(term);
			this.m_Count = 1;
		}

		public boolean shouldBuildLet() {
			TermInfo info = this;
			while (info.m_Count == 1) {
				info = info.m_Parent;
				if (info == null)
					return false;
				if (info.m_Subst != null)
					return false;
			}
			return true;
		}
		
		public void mergeParent(TermInfo parent) {
			if (m_Parent == null) {
				m_Parent = parent;
				m_pDepth = parent.m_pDepth+1;
				return;
			}
			while (m_Parent != parent) {
				if (parent.m_pDepth == m_Parent.m_pDepth) {
					parent = parent.m_Parent;
					m_Parent = m_Parent.m_Parent;
				} else if (parent.m_pDepth > m_Parent.m_pDepth) {
					parent = parent.m_Parent;
				} else {
					m_Parent = m_Parent.m_Parent;
				}
			}
			m_pDepth = m_Parent.m_pDepth + 1;
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			throw new InternalError("No TermInfo for ConstantTerm allowed");
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			if (!isNamed(term))
				visitChild((FormulaLet) walker, term.getSubterm());
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			Term[] args = term.getParameters();
			for (Term t : args)
				visitChild((FormulaLet) walker, t);
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError("Let-Terms should not be in the formula anymore");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// do not recurse into quantified formulas
			// this avoids problem with common terms containing free
			// variables
			//((FormulaLet) walker).visit(term.getSubformula(), this);
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			throw new InternalError("No TermInfo for TermVariable allowed");
		}

		public void visitChild(FormulaLet let, Term term) {
			if (term instanceof TermVariable
				|| term instanceof ConstantTerm) {
				return;
			}
			if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getParameters().length == 0)
				return;
	
			TermInfo child = let.m_Visited.getLast().get(term);
			if (child == null) {
				child = new TermInfo(term);
				let.m_Visited.getLast().put(term, child);
				let.enqueueWalker(child);
			} else {
				child.m_Count++;
			}
		}
	}
	
	static class Transformer implements Walker {
		TermInfo m_TermInfo;
		boolean m_IsCounted;
		public Transformer(TermInfo parent, boolean isCounted) {
			m_TermInfo = parent;
			m_IsCounted = isCounted;
		}
		
		public void walk(NonRecursive engine) {
			FormulaLet let = ((FormulaLet) engine);
			Term term = m_TermInfo.m_Term;
			if (m_IsCounted) {
				let.enqueueWalker(new BuildLet(m_TermInfo));
				m_TermInfo.m_LettedTerms = new ArrayList<TermInfo>();
			}
			if (term instanceof QuantifiedFormula) {
				QuantifiedFormula quant = (QuantifiedFormula) term;
				let.enqueueWalker(new BuildQuantifier(quant));
				let.enqueueWalker
					(new Letter(quant.getSubformula()));
			} else if (term instanceof AnnotatedTerm) {
				AnnotatedTerm at = (AnnotatedTerm) term;
				let.enqueueWalker(new BuildAnnotatedTerm(at));
				if (isNamed(at))
					let.enqueueWalker(new Letter(at.getSubterm()));
				else
					let.enqueueWalker(new Converter(m_TermInfo, at.getSubterm(), m_IsCounted));
			} else if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				let.enqueueWalker(new BuildApplicationTerm(appTerm));
				Term[] params = appTerm.getParameters();
				for (int i = params.length-1; i >= 0; i--)
					let.enqueueWalker(new Converter(m_TermInfo, params[i], m_IsCounted));
			} else {
				let.m_ResultStack.addLast(term);
			}
		}
	}		
	static class Converter implements Walker {
		TermInfo m_Parent;
		Term m_Term;
		boolean m_IsCounted;
		public Converter(TermInfo parent, Term term, boolean isCounted) {
			m_Parent = parent;
			m_Term = term;
			m_IsCounted = isCounted;
		}

		public void walk(NonRecursive engine) {
			FormulaLet let = ((FormulaLet) engine);
			Term child = m_Term;
			TermInfo info = let.m_Visited.getLast().get(child);
			if (info == null) {
				let.m_ResultStack.addLast(child);
				return;
			}
			info.mergeParent(m_Parent);
			if (info.shouldBuildLet() && info.m_Subst == null && 
				(let.m_Filter == null || let.m_Filter.isLettable(child))) {
				Term t = info.m_Term; 
				info.m_Subst = t.getTheory().
					createTermVariable(".cse" + let.m_CseNum++, t.getSort());
			}
			if (m_IsCounted) {
				if (++info.m_Seen == info.m_Count) {
					if (info.m_Subst == null)
						let.enqueueWalker(new Transformer(info, true));
					else {
						let.m_ResultStack.addLast(info.m_Subst);
						TermInfo ancestor = info.m_Parent;
						TermInfo letPos = ancestor;
						while (ancestor != null && ancestor.m_Subst == null) {
							if (ancestor.m_Count > 1)
								letPos = ancestor.m_Parent;
							ancestor = ancestor.m_Parent;
						}
						letPos.m_LettedTerms.add(info);
					}
					return;
				}
			}
			
			if (info.m_Subst != null)
				let.m_ResultStack.addLast(info.m_Subst);
			else
				let.enqueueWalker(new Transformer(info, false));
		}
	}
	
	static class BuildLet implements Walker {
		TermInfo m_TermInfo;
		public BuildLet(TermInfo parent) {
			m_TermInfo = parent;
		}
		
		public void walk(NonRecursive engine) {
			FormulaLet let = ((FormulaLet) engine);
			List<TermInfo> lettedTerms = m_TermInfo.m_LettedTerms;
			if (lettedTerms.isEmpty())
				return;
			TermVariable[] tvs = new TermVariable[lettedTerms.size()];
			let.enqueueWalker(this);
			let.enqueueWalker(new BuildLetTerm(tvs));
			int i = 0;
			for (TermInfo ti : lettedTerms) {
				tvs[i++] = ti.m_Subst;
				let.enqueueWalker(new Transformer(ti, true));
			}
			lettedTerms.clear();
		}
	}
	
	static class BuildLetTerm implements Walker {
		TermVariable[] m_Vars;
		public BuildLetTerm(TermVariable[] vars) {
			m_Vars = vars;
		}
		public void walk(NonRecursive engine) {
			FormulaLet let = (FormulaLet)engine;
			Term[] values = new Term[m_Vars.length];
			for (int i = 0; i < values.length; i++)
				values[i] = let.m_ResultStack.removeLast();
			Term newBody = let.m_ResultStack.removeLast();
			Theory theory = newBody.getTheory();
			Term result = theory.let(m_Vars, values, newBody);
			let.m_ResultStack.addLast(result);
		}
	}

	static class BuildApplicationTerm implements Walker {
		ApplicationTerm m_OldTerm;
		public BuildApplicationTerm(ApplicationTerm term) {
			m_OldTerm = term;
		}
		public void walk(NonRecursive engine) {
			FormulaLet let = (FormulaLet)engine;
			Term[] newParams = let.getTerms(m_OldTerm.getParameters());
			Term result = m_OldTerm;
			if (newParams != m_OldTerm.getParameters()) {
				Theory theory = m_OldTerm.getTheory();
				result = theory.term(m_OldTerm.getFunction(), newParams);
			}
			let.m_ResultStack.addLast(result);
		}
	}

	static class BuildQuantifier implements Walker {
		QuantifiedFormula m_OldTerm;
		public BuildQuantifier(QuantifiedFormula term) {
			m_OldTerm = term;
		}
		public void walk(NonRecursive engine) {
			FormulaLet let = (FormulaLet)engine;
			Term newBody = let.m_ResultStack.removeLast();
			Term result = m_OldTerm;
			if (newBody != m_OldTerm.getSubformula()) {
				Theory theory = m_OldTerm.getTheory();
				if (m_OldTerm.getQuantifier() == QuantifiedFormula.EXISTS)
					result = theory.exists(m_OldTerm.getVariables(), newBody);
				else
					result = theory.forall(m_OldTerm.getVariables(), newBody);
			}
			let.m_ResultStack.addLast(result);
		}
	}

	static class BuildAnnotatedTerm implements Walker {
		AnnotatedTerm m_OldTerm;
		public BuildAnnotatedTerm(AnnotatedTerm term) {
			m_OldTerm = term;
		}
		public void walk(NonRecursive engine) {
			FormulaLet let = (FormulaLet)engine;
			Term newBody = let.m_ResultStack.removeLast();
			Term result = m_OldTerm;
			if (newBody != m_OldTerm.getSubterm()) {
				Theory theory = m_OldTerm.getTheory();
				result = theory.annotatedTerm(m_OldTerm.getAnnotations(), newBody);
			}
			let.m_ResultStack.addLast(result);
		}
	}

	private static boolean isNamed(AnnotatedTerm at) {
		for (Annotation a : at.getAnnotations()) {
			if (a.getKey().equals(":named")) {
				return true;
			}
		}
		return false;
	}

	public Term[] getTerms(Term[] oldArgs) {
		Term[] newArgs = oldArgs;
		for (int i = oldArgs.length - 1; i >= 0; i--) {
			Term newTerm = m_ResultStack.removeLast();
			if (newTerm != oldArgs[i]) {
				if (newArgs == oldArgs)
					newArgs = oldArgs.clone();
				newArgs[i] = newTerm;
			}
		}
		return newArgs;
	}
}
