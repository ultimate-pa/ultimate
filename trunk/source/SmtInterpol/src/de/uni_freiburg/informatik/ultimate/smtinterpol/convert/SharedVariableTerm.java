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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

/**
 * For now, this is just a place holder for TermVariables.  This class prevents
 * calls to share or shareWithLinAr
 * @author Juergen Christ
 */
public class SharedVariableTerm extends SharedTermOld {
	
	// The var that is wrapped within this shared term
	private final TermVariable m_Var;
	
	public SharedVariableTerm(ConvertFormula converter, TermVariable var) {
		super(converter);
		m_Var = var;
	}

	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		return m_Var;
	}

	@Override
	public Sort getSort() {
		return m_Var.getSort();
	}

	@Override
	public CCTerm toCCTerm() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append(m_Var);
	}

	@Override
	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}

	@Override
	public void share() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public void shareWithLinAr() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public FlatFormula createEquality(SharedTermOld other) {
		// TODO Is this what we want?
		return new EqualityFormula(m_converter, this, other);
	}

	@Override
	public void setLinVar(Rational factor, LinVar linvar, Rational offset) {
		throw new InternalError("This should not be called!");
	}

	@Override
	public void unshareLA() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public void unshareCC() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public LinVar getLinVar() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public Rational getOffset() {
		throw new InternalError("This should not be called!");
	}

	@Override
	public Rational getFactor() {
		throw new InternalError("This should not be called!");
	}

}
