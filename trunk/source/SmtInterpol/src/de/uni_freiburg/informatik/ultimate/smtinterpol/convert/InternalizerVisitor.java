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

public class InternalizerVisitor extends AbstractFlatTermOnceVisitor {

	private boolean m_UnderFunc = false;
	
	@Override
	public void visit(AffineTerm at) {
		if (m_UnderFunc)
			at.toShared().shareWithLinAr();
		if (!visited(at))	
			super.visit(at);
	}

	@Override
	public void visit(DivideTerm dt) {
		if (!visited(dt)) {
			dt.createAxioms();
			super.visit(dt);
		}
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		if (!visited(fat)) {
			boolean oldUnderFunc = m_UnderFunc;
			m_UnderFunc = true;
			super.visit(fat);
			if (fat.m_Parameters.length != 0)
				fat.toCCTerm();
			m_UnderFunc = oldUnderFunc;
		}
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		if (!visited(itet)) {
			super.visit(itet);
			itet.createAxioms();
		}
	}

	@Override
	public void visit(SharedAffineTerm st) {
		if (!visited(st)) {
			st.shareWithLinAr();
			super.visit(st);
		}
	}

	@Override
	public void visit(EqualityFormula ef) {
		if (!visited(ef)) {
			super.visit(ef);
			// Force creation of the equality literal to ensure correct results
			// from get-value
			ef.getLiteral();
		}
	}

	@Override
	public void reset() {
		m_UnderFunc = false;
		super.reset();
	}
	
}
