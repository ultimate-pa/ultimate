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
 * Lift if-then-else terms to Boolean level.  Lifting is performed in two steps:
 * A TermITELifter detects both, TermITEs that should be lifted and the correct
 * position of the new ITE.  A TermITERemover is used to build the new formula.
 * @author Juergen Christ
 */
public class TermITELifter extends AbstractFlatTermTransformer {
	
	/**
	 * Helper class used to communicate the detection of a term-ITE to the next
	 * Boolean level.  I use an exception here to easily unwind the visitor
	 * stack.  Since visit does not declare any exception, I use a
	 * {@link RuntimeException}.
	 * @author Juergen Christ
	 */
	@SuppressWarnings("serial")
	private static final class TermITEDetected extends RuntimeException {
		IfThenElseTerm m_TermITE;
		public TermITEDetected(IfThenElseTerm termITE) {
			m_TermITE = termITE;
		}
	}
	
	private final TermITEDetected m_Detected = new TermITEDetected(null);
	
	private int m_NumLifted = 0;
	
	/**
	 * Class to remove a termITE from the flat term DAG.  Note that this class
	 * only removes one branch, but not both.  So you need to accept it twice
	 * to completely remove a termITE.  Don't forget to retrieve the result of
	 * the first removal operation.
	 * @author Juergen Christ
	 */
	private static class TermITERemover extends AbstractFlatTermTransformer {

		IfThenElseTerm m_Itet;
		FlatTerm m_Subst;
		
		TermITERemover(ConvertFormula converter) {
			super(converter);
		}

		@Override
		public void visit(IfThenElseTerm itet) {
			if (itet == m_Itet)
				register(itet, m_Subst);
			else
				super.visit(itet);
		}
		
		public void reset(IfThenElseTerm itet, FlatTerm subst) {
			super.reset();
			m_Itet = itet;
			m_Subst = subst;
		}
		
	}
	
	private final TermITERemover m_Remover;
	
	public TermITELifter(ConvertFormula converter) {
		super(converter);
		m_Remover = new TermITERemover(converter);
	}

	@Override
	public void visit(EqualityFormula ef) {
		try {
			super.visit(ef);
		} catch (TermITEDetected termITE) {
			FlatTerm newft = removeTermITE(ef, termITE.m_TermITE);
			// Remove possibly left termITEs
			newft.accept(this);
			register(ef, get(newft));
		}
	}

	@Override
	public void visit(IfThenElseTerm itet) {
		m_Detected.m_TermITE = itet;
		throw m_Detected;
	}

	@Override
	public void visit(LeqZeroFormula lzf) {
		try {
			super.visit(lzf);
		} catch (TermITEDetected termITE) {
			FlatTerm newft = removeTermITE(lzf, termITE.m_TermITE);
			// Remove possibly left termITEs
			newft.accept(this);
			register(lzf, get(newft));
		}
	}

	@Override
	public void visit(FlatApplicationTerm fat) {
		if (!visited(fat))
			super.visit(fat);
	}
	
	/**
	 * Remove a term ITE under a flat term.  Note that the result of this
	 * operation might still contain term ITEs if the original flat term
	 * contained at least two different term ITEs.
	 * @param ft   The flat term under which <code>itet</code> should occur.
	 * @param itet The term ITE to remove.
	 * @return A Boolean ITE without the given termITE.
	 */
	private final FlatTerm removeTermITE(FlatTerm ft, IfThenElseTerm itet) {
		// Produce true term
		m_Remover.reset(itet, itet.mThen);
		ft.accept(m_Remover);
		FlatFormula trueTerm = (FlatFormula)m_Remover.get(ft);
		// Produce false term
		m_Remover.reset(itet, itet.mElse);
		ft.accept(m_Remover);
		FlatFormula falseTerm = (FlatFormula)m_Remover.get(ft);
		FlatTerm res = m_converter.createIfThenElse(itet.mCond, trueTerm, falseTerm);
		++m_NumLifted;
//		System.err.println();
//		System.err.println("Removing " + itet);
//		System.err.println("  from " + ft);
//		System.err.println("    yields " + res);
//		System.err.println();
		return res;
	}

	public int getNumLifted() {
		return m_NumLifted;
	}
	
}
