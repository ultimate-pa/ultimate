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
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IdentityHashSet;

public class AbstractFlatTermOnceVisitor extends AbstractFlatTermVisitor {
	
	// Since FlatTerms are unified, we have ft1.equals(ft2) <=> ft1 == ft2
	// Hence, I use an IdentityHashSet since it should provide better
	// performance than a regular HashSet.
	protected IdentityHashSet<FlatTerm> m_Visited =
		new IdentityHashSet<FlatTerm>();

	/**
	 * Is the given flat term unvisited.  Note that this function has the side
	 * effect to mark the flat term as visited.
	 * @param t The flat term to visit
	 * @return Has the flat term not already been visited?
	 */
	protected final boolean unvisited(FlatTerm t) {
		return m_Visited.add(t);
	}
	
	/**
	 * Has the given flat term already been visited.  This function is free of
	 * side effects.
	 * @param t The flat term to visit.
	 * @return Has the flat term already been visited?
	 */
	protected final boolean visited(FlatTerm t) {
		return m_Visited.contains(t);
	}
	
	public void reset() {
		m_Visited.clear();
	}

	@Override
	public void visit(AffineTerm at) {
		if (unvisited(at))
			super.visit(at);
	}

	@Override
	public void visit(ClauseFormula cf) {
		if (unvisited(cf))
			super.visit(cf);
	}

	@Override
	public void visit(DivideTerm dt) {
		if (unvisited(dt))
			super.visit(dt);
	}

	@Override
	public void visit(EqualityFormula ef) {
		if (unvisited(ef))
			super.visit(ef);
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		if (unvisited(fat))
			super.visit(fat);
	}

	@Override
	public void visit(ForallFormula ff) {
		if (unvisited(ff))
			super.visit(ff);
	}

	@Override
	public void visit(IfThenElseFormula itef) {
		if (unvisited(itef))
			super.visit(itef);
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		if (unvisited(itet))
			super.visit(itet);
	}

	@Override
	public void visit(LeqZeroFormula lzf) {
		if (unvisited(lzf))
			super.visit(lzf);
	}

	@Override
	public void visit(LiteralFormula lf) {
		if (unvisited(lf))
			super.visit(lf);
	}

	@Override
	public void visit(NegClauseFormula ncf) {
		if (unvisited(ncf))
			super.visit(ncf);
	}

	@Override
	public void visit(NegForallFormula nff) {
		if (unvisited(nff))
			super.visit(nff);
	}

	@Override
	public void visit(SharedAffineTerm st) {
		if (unvisited(st))
			super.visit(st);
	}

	@Override
	public void visit(NegatedFormula efnf) {
		if (unvisited(efnf))
			super.visit(efnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LeqZeroFormula.NegatedFormula lzfnf) {
		if (unvisited(lzfnf))
			super.visit(lzfnf);
	}

	@Override
	public void visit(
			de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LiteralFormula.NegatedFormula lfnf) {
		if (unvisited(lfnf))
			super.visit(lfnf);
	}
	
}
