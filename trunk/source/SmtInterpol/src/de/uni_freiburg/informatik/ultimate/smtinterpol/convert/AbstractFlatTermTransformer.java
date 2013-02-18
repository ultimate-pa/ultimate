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
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityFormula.NegatedFormula;

public abstract class AbstractFlatTermTransformer implements FlatTermVisitor {

	private Map<FlatTerm, FlatTerm> m_Transformations; 
	
	protected final ConvertFormula m_converter;
	
	protected AbstractFlatTermTransformer(ConvertFormula converter) {
		// Use a weak referencing hash map here to get rid of intermediate
		// objects in case of recursive calls (e.g., in TermITELifter).
		m_Transformations = new WeakHashMap<FlatTerm, FlatTerm>();
		m_converter = converter;
	}
	
	public FlatTerm transform(FlatTerm t) {
		t.accept(this);
		return m_Transformations.get(t);
	}
	
	protected boolean visited(FlatTerm t) {
		return m_Transformations.containsKey(t);
	}

	protected void register(FlatTerm oldft, FlatTerm newft) {
		m_Transformations.put(oldft, newft);
	}
	
	protected FlatTerm get(FlatTerm f) {
		return m_Transformations.get(f);
	}
	
	@Override
	public void visit(AffineTerm at) {
		if (visited(at))
			return;
		AffineTerm res =
			new AffineTerm(m_converter, at.getConstant(), at.getSort());
		for (Map.Entry<FlatTerm, Rational> me : at.getSummands().entrySet()) {
			me.getKey().accept(this);
			res = res.add(m_Transformations.get(me.getKey()).
					toAffineTerm().mul(me.getValue()));
		}
		m_Transformations.put(at, res);
	}

	@Override
	public void visit(ClauseFormula cf) {
		if (visited(cf))
			return;
		for (FlatFormula sub : cf.subformulas)
			sub.accept(this);
		boolean changed = false;
		Set<FlatFormula> newsubs = new HashSet<FlatFormula>();
		for (FlatFormula f : cf.subformulas) {
			FlatTerm transformed = m_Transformations.get(f);
			if (transformed == m_converter.TRUE) {
				// This clause formula is now true and can be removed.
				register(cf, transformed);
				return;
			}
			if (transformed != m_converter.FALSE)
				newsubs.add((FlatFormula) transformed);
			changed |= transformed != f;
		}
		register(cf, changed ? m_converter.createClauseFormula(newsubs) : cf);
	}

	@Override
	public void visit(DivideTerm dt) {
		if (visited(dt))
			return;
		dt.getAffineTerm().accept(this);
		m_converter.createDivideTerm(
				(AffineTerm) m_Transformations.get(dt.getAffineTerm()),
				dt.m_divisor);
	}

	@Override
	public void visit(EqualityFormula ef) {
		if (visited(ef))
			return;
		ef.mLhs.accept(this);
		ef.mRhs.accept(this);
		FlatTerm t1 = m_Transformations.get(ef.mLhs);
		FlatTerm t2 = m_Transformations.get(ef.mRhs);
		if (t1 == t2)
			m_Transformations.put(ef, m_converter.TRUE);
		else
			m_Transformations.put(ef, (t1 != ef.mLhs || t2 != ef.mRhs) ?
					m_converter.createEqualityFormula(t1, t2) : ef);
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		if (visited(fat))
			return;
		for (FlatTerm t : fat.m_Parameters)
			t.accept(this);
		boolean changed = false;
		FlatTerm[] newParams = new FlatTerm[fat.m_Parameters.length];
		for (int i = 0; i < newParams.length; ++i) {
			FlatTerm t = fat.m_Parameters[i];
			FlatTerm newt = m_Transformations.get(t);
			newParams[i] = newt;
			changed |= newt != t;
		}
		m_Transformations.put(fat, changed ?
				m_converter.createApplicationTerm(fat.m_Symbol, newParams) :
					fat);
	}

	@Override
	public void visit(ForallFormula ff) {
		if (visited(ff))
			return;
		// TODO
	}

	@Override
	public void visit(IfThenElseFormula itef) {
		if (visited(itef))
			return;
		itef.cond.accept(this);
		itef.thenForm.accept(this);
		itef.elseForm.accept(this);
		FlatFormula cond = (FlatFormula) m_Transformations.get(itef.cond);
		FlatFormula thenForm =
			(FlatFormula) m_Transformations.get(itef.thenForm);
		FlatFormula elseForm =
			(FlatFormula) m_Transformations.get(itef.elseForm);
		m_Transformations.put(itef,
				(itef.cond != cond || itef.thenForm != thenForm ||
						itef.elseForm != elseForm) ?
								m_converter.createIfThenElse(
										cond, thenForm, elseForm) : itef);
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		if (visited(itet))
			return;
		itet.mCond.accept(this);
		itet.mThen.accept(this);
		itet.mElse.accept(this);
		FlatFormula cond = (FlatFormula) m_Transformations.get(itet.mCond);
		FlatTerm thenForm = m_Transformations.get(itet.mThen);
		FlatTerm elseForm = m_Transformations.get(itet.mElse);
		m_Transformations.put(itet,
				(itet.mCond != cond || itet.mThen != thenForm ||
						itet.mElse != elseForm) ?
								m_converter.createIteTerm(
										cond, thenForm.toShared(),
										elseForm.toShared()) : itet);

	}

	@Override
	public void visit(LeqZeroFormula lzf) {
		if (visited(lzf))
			return;
		lzf.mTerm.accept(this);
		AffineTerm term = (AffineTerm) m_Transformations.get(lzf.mTerm);
		m_Transformations.put(lzf, (term != lzf.mTerm) ?
				m_converter.createLeq0Formula(term) : lzf);
	}

	@Override
	public void visit(LiteralFormula lf) {
		if (visited(lf))
			return;
		m_Transformations.put(lf, lf);
	}

	@Override
	public void visit(NegClauseFormula ncf) {
		if (visited(ncf))
			return;
		ncf.negate().accept(this);
		FlatFormula tmp = (FlatFormula) m_Transformations.get(ncf.negate());
		m_Transformations.put(ncf, tmp != ncf.negate() ? tmp.negate() : ncf);
	}

	@Override
	public void visit(NegForallFormula nff) {
		if (visited(nff))
			return;
		// TODO
	}

	@Override
	public void visit(SharedAffineTerm st) {
		if (visited(st))
			return;
		st.m_affineTerm.accept(this);
		AffineTerm term = (AffineTerm) m_Transformations.get(st.m_affineTerm);
		m_Transformations.put(st, term != st.m_affineTerm ?
				m_converter.createSharedAffineTerm(term) : st);
	}

	@Override
	public void visit(NegatedFormula efnf) {
		if (visited(efnf))
			return;
		efnf.negate().accept(this);
		FlatFormula neg = (FlatFormula) m_Transformations.get(efnf.negate());
		m_Transformations.put(efnf, neg != efnf.negate() ? neg.negate() : efnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LeqZeroFormula.NegatedFormula efnf) {
		if (visited(efnf))
			return;
		efnf.negate().accept(this);
		FlatFormula neg = (FlatFormula) m_Transformations.get(efnf.negate());
		m_Transformations.put(efnf, neg != efnf.negate() ? neg.negate() : efnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LiteralFormula.NegatedFormula efnf) {
		if (visited(efnf))
			return;
		efnf.negate().accept(this);
		FlatFormula neg = (FlatFormula) m_Transformations.get(efnf.negate());
		m_Transformations.put(efnf, neg != efnf.negate() ? neg.negate() : efnf);
	}
	
	@Override
	public void visit(SharedVariableTerm svt) {
		m_Transformations.put(svt, svt);
	}

	@Override
	public void visitTrue(FlatFormula fftrue) {
		if (visited(fftrue))
			return;
		m_Transformations.put(fftrue, fftrue);
	}

	@Override
	public void visitFalse(FlatFormula fffalse) {
		if (visited(fffalse))
			return;
		m_Transformations.put(fffalse, fffalse);
	}

	public void reset() {
		m_Transformations.clear();
	}

}
