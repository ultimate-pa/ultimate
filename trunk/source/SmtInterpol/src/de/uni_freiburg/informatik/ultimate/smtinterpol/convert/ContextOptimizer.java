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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityFormula.NegatedFormula;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

/**
 * Contextual rewriting and path optimization.  Does not descend into
 * non-Boolean functions.
 * 
 * Rewrites:
 * <pre>
 * (or termlist) -> 
 *   foreach term in termlist:
 *     assume (not (or termlist without term))
 *     simplify term
 *     
 * (and termlist) ->
 *   foreach term in termlist:
 *     assume (and termlist without term)
 *     simplify term
 *     
 * (ite cond then else) ->
 *   {
 *     assume cond
 *     simplify then
 *   }{
 *     assume (not cond)
 *     simplify else
 *   }
 * 
 * literal ->
 *   if literal is assumed
 *     true
 *   else if (not literal) is assumed
 *     false
 *   else
 *     literal
 * </pre>
 * @author Juergen Christ
 */
public class ContextOptimizer extends AbstractFlatTermTransformer {

	/* Further optimizations to try:
	 * Optimize linear arithmetic:
	 *   keep list of assumed upper and lower bounds on linear combinations of
	 *   variables (\sum_i c_i t_i)
	 * Check:
	 *   1) LeqZeroFormula \sum_i c_i t_i + c <(=) 0
	 *     If assumed lower bound for \sum_i c_i t_i is greater (equal) than -c,
	 *     transform to false
	 *     If assumed upper bound is less (equal) than -c, transform to true
	 * No clue how expensive that would be.
	 * TODO Try this once...
	 */
	
	private ScopedHashSet<FlatFormula> m_AssumedTrue;
	private ScopedHashSet<FlatFormula> m_AssumedFalse;
	
	public ContextOptimizer(ConvertFormula converter) {
		super(converter);
		m_AssumedTrue = new ScopedHashSet<FlatFormula>();
		m_AssumedFalse = new ScopedHashSet<FlatFormula>();
	}

	/**
	 * Add formulas that can be assumed to be false.
	 * @param f Formula to add.
	 */
	private void addAssumptions(FlatFormula f) {
		m_AssumedFalse.addAll(f.getSubFormulas());
		m_AssumedTrue.add(f.negate());
	}
	
	/**
	 * Check whether a formula or its negation is assumed.  As a side effect,
	 * this function also registers the formula if it is already assumed.
	 * @param f Formula to check
	 * @return <code>true</code> if the formula or its negation is assumed. 
	 */
	private boolean checkAssumption(FlatFormula f) {
		if (m_AssumedFalse.contains(f)) {
			register(f, m_converter.FALSE);
			return true;
		}
		if (m_AssumedTrue.contains(f)) {
			register(f, m_converter.TRUE);
			return true;
		}
		return false;
	}
	
	@Override
	public void visit(AffineTerm at) {
		throw new AssertionError("Should never be called!");
	}

	@Override
	public void visit(ClauseFormula cf) {
		if (checkAssumption(cf))
			return;
		boolean changed = false;
		Set<FlatFormula> newsubs = new HashSet<FlatFormula>();
		for (int i = 0; i < cf.subformulas.length; ++i) {
			FlatFormula f = cf.subformulas[i];
			m_AssumedTrue.beginScope();
			m_AssumedFalse.beginScope();
			for (FlatFormula sub : newsubs)
				addAssumptions(sub);
			for (int j = i + 1; j < cf.subformulas.length; ++j)
				addAssumptions(cf.subformulas[j]);
			f.accept(this);
			m_AssumedFalse.endScope();
			m_AssumedTrue.endScope();
			FlatFormula newf = (FlatFormula) get(f);
			if (newf == m_converter.TRUE) {
				// Clause is trivially valid
				register(cf, newf);
				return;
			}
			if (newf != m_converter.FALSE) {
				newsubs.addAll(newf.getSubFormulas());
			}
			changed |= newf != f;
		}
		register(cf, changed ? m_converter.createClauseFormula(newsubs) : cf);
	}

	@Override
	public void visit(DivideTerm dt) {
		throw new AssertionError("Should never be called!");
	}

	@Override
	public void visit(EqualityFormula ef) {
		if (checkAssumption(ef))
			return;
		if (ef.mLhs.getSort() == m_converter.m_Theory.getBooleanSort()) {
			ef.mLhs.accept(this);
			ef.mRhs.accept(this);
			FlatTerm lhs = get(ef.mLhs);
			FlatTerm rhs = get(ef.mRhs);
			register(ef, (lhs != ef.mLhs || rhs != ef.mRhs) ? 
					m_converter.createEqualityFormula(lhs, rhs) : ef);
		} else
			// There is nothing we can do here...
			register(ef, ef);
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		throw new AssertionError("Should never be called!");
	}

	@Override
	public void visit(ForallFormula ff) {
		// TODO
	}

	@Override
	public void visit(IfThenElseFormula itef) {
		if (checkAssumption(itef))
			return;
		// First optimize the condition
		itef.cond.accept(this);
		FlatFormula cond = (FlatFormula) get(itef.cond);
		if (cond == m_converter.TRUE) {
			itef.thenForm.accept(this);
			register(itef, get(itef.thenForm));
		} else if (cond == m_converter.FALSE) {
			itef.elseForm.accept(this);
			register(itef, get(itef.elseForm));
		} else {
			// Not a trivial ite.  Simplify parts...
			m_AssumedTrue.beginScope();
			m_AssumedFalse.beginScope();
			addAssumptions(cond.negate());
			itef.thenForm.accept(this);
			m_AssumedFalse.endScope();
			m_AssumedTrue.endScope();
			m_AssumedTrue.beginScope();
			m_AssumedFalse.beginScope();
			addAssumptions(cond);
			itef.elseForm.accept(this);
			m_AssumedFalse.endScope();
			m_AssumedTrue.endScope();
			FlatFormula tf = (FlatFormula) get(itef.thenForm);
			FlatFormula ef = (FlatFormula) get(itef.elseForm);
			register(itef, (cond != itef.cond || tf != itef.thenForm || 
					ef != itef.elseForm) ?
							m_converter.createIfThenElse(cond, tf, ef) : itef);
		}
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		throw new AssertionError("Should never be called!");
	}

	@Override
	public void visit(LeqZeroFormula lzf) {
		if (!checkAssumption(lzf))
			// There is nothing we can do here...
			register(lzf, lzf);
	}

	@Override
	public void visit(LiteralFormula lf) {
		if (!checkAssumption(lf))
			// There is nothing we can do here...
			register(lf, lf);
	}

	@Override
	public void visit(NegForallFormula nff) {
		// TODO
	}

	@Override
	public void visit(SharedAffineTerm st) {
		throw new AssertionError("Should never be called!");
	}

	@Override
	public void visit(NegClauseFormula ncf) {
		if (checkAssumption(ncf))
			return;
		ncf.positive.accept(this);
		FlatFormula positive = (FlatFormula) get(ncf.positive);
		register(ncf, positive != ncf.positive ? positive.negate() : ncf);
	}

	@Override
	public void visit(NegatedFormula efnf) {
		if (!checkAssumption(efnf))
			register(efnf, efnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LeqZeroFormula.NegatedFormula efnf) {
		if (!checkAssumption(efnf))
			register(efnf, efnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LiteralFormula.NegatedFormula efnf) {
		if (!checkAssumption(efnf))
			register(efnf, efnf);
	}
}
