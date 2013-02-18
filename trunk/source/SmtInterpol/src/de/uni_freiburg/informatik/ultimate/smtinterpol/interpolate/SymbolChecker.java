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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SymbolChecker extends TermTransformer {

	private Map<FunctionSymbol, Integer> m_LeftAllowed;
	private Map<FunctionSymbol, Integer> m_RightAllowed;
	private HashSet<FunctionSymbol> m_LeftErrors;
	private HashSet<FunctionSymbol> m_RightErrors;
	private Set<FunctionSymbol> m_Globals;
	
	public SymbolChecker(Set<FunctionSymbol> globals) {
		m_Globals = globals;
	}
	
	/**
	 * Check whether an interpolant contains only allowed symbols.
	 * @param interpolant  The interpolant.
	 * @param leftAllowed  The symbols allowed from the left-hand side.
	 * @param rightAllowed The symbols allowed from the right-hand side.
	 * @return <code>true</code> if an error has been detected.
	 */
	public final boolean check(Term interpolant,
			Map<FunctionSymbol, Integer> leftAllowed,
			Map<FunctionSymbol, Integer> rightAllowed) {
		m_LeftAllowed = leftAllowed;
		m_RightAllowed = rightAllowed;
		m_LeftErrors = new HashSet<FunctionSymbol>();
		m_RightErrors = new HashSet<FunctionSymbol>();
		transform(interpolant);
		return !(m_LeftErrors.isEmpty() && m_RightErrors.isEmpty());
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		FunctionSymbol fs = appTerm.getFunction();
		if (!fs.isIntern() && !m_Globals.contains(fs)) {
			Integer left = m_LeftAllowed.get(fs);
			Integer right = m_RightAllowed.get(fs);
			if (left == null && right == null)
				throw new InternalError("Detected new symbol in interpolant: " + fs);
			else if (left == null)
				m_RightErrors.add(fs);
			else if (right - left <= 0)
				m_LeftErrors.add(fs);
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
	
	public Set<FunctionSymbol> getLeftErrors() {
		return m_LeftErrors;
	}
	
	public Set<FunctionSymbol> getRightErrors() {
		return m_RightErrors;
	}
	
}
