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

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


/**
 * A FlatTerm is the base class of all terms produced by the converter.
 * Every smt term is converted to a flat term, that records information about
 * usage, the corresponding CCTerm/LinVar in the theories, etc.
 * Also FlatFormula is a sub-class of FlatTerm, to represent complex formulas,
 * and record auxiliary variables needed to convert to CNF.  
 * 
 * @author hoenicke
 */
public abstract class FlatTerm {
	static int counter = 0;
	int ctr = counter++;
	ConvertFormula m_converter;
	
	/* disable default constructor. */
	@SuppressWarnings("unused")
	private FlatTerm(){}
	/**
	 * Create a new flat term. 
	 * @param converter the formula converter used.
	 */
	public FlatTerm(ConvertFormula converter) {
		m_converter = converter;
	}

	/**
	 * Gets an smtlib term that equals this flat term.
	 * @param useAuxVars true if auxVars should be used.
	 * @return the smtlib term.
	 */
	public abstract Term getSMTTerm(boolean useAuxVars);
	
	/**
	 * Gets an smtlib term that equals this flat term.
	 * @return the smtlib term.
	 */
	public final Term getSMTTerm() {
		return getSMTTerm(false);
	}
	
	/**
	 * Computes the smtlib sort of this term.
	 * @return the smtlib sort of this term.
	 */
	public abstract Sort getSort();

	public AffineTerm toAffineTerm() {
		return new AffineTerm(this);
	}
	
	public abstract SharedTermOld toShared();
	public abstract CCTerm toCCTerm();
	public int hashCode() {
		return ctr;
	}
	
	public abstract void toStringHelper(StringBuilder sb, 
			                            HashSet<FlatTerm> visited);
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		toStringHelper(sb, new HashSet<FlatTerm>());
		return sb.toString();
	}
	
	public abstract void accept(FlatTermVisitor visitor);
}
