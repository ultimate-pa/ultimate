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

import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IdentityHashSet;

/**
 * This optimizer is merely a hack for the nec-smt benchmarks from the
 * competition.  These benchmarks produce (after lifting) a lot of nested ITEs
 * where the condition of an ITE occurs as the condition of a nested ITE.
 * This optimizer tries to simplify this. 
 * @author Juergen Christ
 */
public class PathOptimizer extends AbstractFlatTermTransformer {

	private IdentityHashSet<FlatFormula> m_ItePaths =
		new IdentityHashSet<FlatFormula>();
	
	protected PathOptimizer(ConvertFormula converter) {
		super(converter);
	}

	@Override
	public void visit(IfThenElseFormula itef) {
		itef.cond.accept(this);
		FlatFormula cond = itef.cond;
		FlatFormula ncond = (FlatFormula)get(cond);
		if (m_ItePaths.contains(cond) || m_ItePaths.contains(ncond)) {
			// We only need the then part
			itef.thenForm.accept(this);
			register(itef, get(itef.thenForm));
		} else if (m_ItePaths.contains(cond.negate()) ||
				m_ItePaths.contains(ncond.negate())) {
			// We only need the else part
			itef.elseForm.accept(this);
			register(itef, get(itef.elseForm));
		} else {
			m_ItePaths.add(cond);
			m_ItePaths.add(ncond);
			itef.thenForm.accept(this);
			m_ItePaths.remove(cond);
			m_ItePaths.remove(ncond);
			m_ItePaths.add(cond.negate());
			m_ItePaths.add(ncond.negate());
			itef.elseForm.accept(this);
			m_ItePaths.remove(cond.negate());
			m_ItePaths.remove(ncond.negate());
			FlatFormula thenForm = (FlatFormula)get(itef.thenForm);
			FlatFormula elseForm = (FlatFormula)get(itef.elseForm);
			register(itef,
				(itef.cond != cond || itef.thenForm != thenForm ||
						itef.elseForm != elseForm) ?
								m_converter.createIfThenElse(
										cond, thenForm, elseForm) : itef);
		}
	}

}
