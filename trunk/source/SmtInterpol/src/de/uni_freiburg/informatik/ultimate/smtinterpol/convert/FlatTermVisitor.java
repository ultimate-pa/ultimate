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

/**
 * A visitor for flat formulas.
 * @author Juergen Christ
 */
public interface FlatTermVisitor {
	public void visit(AffineTerm at);
	public void visit(ClauseFormula cf);
	public void visit(DivideTerm dt);
	public void visit(EqualityFormula ef);
	public void visit(FlatApplicationTerm fat);
	public void visit(ForallFormula ff);
	public void visit(IfThenElseFormula itef);
	public void visit(IfThenElseTerm itet);
	public void visit(LeqZeroFormula lzf);
	public void visit(LiteralFormula lf);
	public void visit(NegClauseFormula ncf);
	public void visit(NegForallFormula nff);
	public void visit(SharedAffineTerm st);
	public void visit(EqualityFormula.NegatedFormula efnf);
	public void visit(LeqZeroFormula.NegatedFormula lzfnf);
	public void visit(LiteralFormula.NegatedFormula lfnf);
	public void visitTrue(FlatFormula fftrue);
	public void visitFalse(FlatFormula fffalse);
	public void visit(SharedVariableTerm sharedVariableTerm);
}
