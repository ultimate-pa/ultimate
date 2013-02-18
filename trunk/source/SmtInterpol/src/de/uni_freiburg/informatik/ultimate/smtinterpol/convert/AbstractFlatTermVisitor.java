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

import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityFormula.NegatedFormula;

public class AbstractFlatTermVisitor implements FlatTermVisitor {

	@Override
	public void visit(AffineTerm at) {
		for (FlatTerm t : at.getSummands().keySet())
			t.accept(this);
	}

	@Override
	public void visit(ClauseFormula cf) {
		for (FlatFormula f : cf.subformulas)
			f.accept(this);
	}

	@Override
	public void visit(DivideTerm dt) {
		dt.getAffineTerm().accept(this);
	}

	@Override
	public void visit(EqualityFormula ef) {
		ef.mLhs.accept(this);
		ef.mRhs.accept(this);
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		for (FlatTerm t : fat.m_Parameters)
			t.accept(this);
	}

	@Override
	public void visit(ForallFormula ff) {
		// TODO
	}

	@Override
	public void visit(IfThenElseFormula itef) {
		itef.cond.accept(this);
		itef.thenForm.accept(this);
		itef.elseForm.accept(this);
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		itet.mCond.accept(this);
		itet.mThen.accept(this);
		itet.mElse.accept(this);
	}

	@Override
	public void visit(LeqZeroFormula lzf) {
		lzf.mTerm.accept(this);
	}

	@Override
	public void visit(LiteralFormula lf) {}

	@Override
	public void visit(NegClauseFormula ncf) {
		for (FlatFormula f : ((ClauseFormula)ncf.negate()).subformulas)
			f.negate().accept(this);
	}

	@Override
	public void visit(NegForallFormula nff) {
		// TODO
	}

	@Override
	public void visit(SharedAffineTerm st) {
		st.m_affineTerm.accept(this);
	}

	@Override
	public void visit(NegatedFormula efnf) {
		efnf.negate().accept(this);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LeqZeroFormula.NegatedFormula lzfnf) {
		lzfnf.negate().accept(this);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LiteralFormula.NegatedFormula lfnf) {
		lfnf.negate().accept(this);
	}

	@Override
	public void visit(SharedVariableTerm svt) {}
	
	@Override
	public void visitTrue(FlatFormula fftrue) {}

	@Override
	public void visitFalse(FlatFormula fffalse) {}
}
