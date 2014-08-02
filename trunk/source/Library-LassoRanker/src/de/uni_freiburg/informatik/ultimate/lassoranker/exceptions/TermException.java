/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.exceptions;

import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * This is an abstract superclass of exceptions that occur when handling terms.
 * It carries an error message as well as a term instance.
 * 
 * @author Jan Leike
 */
public class TermException extends Exception {
	private static final long serialVersionUID = 628015504018345983L;
	
	protected final Term m_term;
	
	public TermException(String message) {
		super(message);
		m_term = null;
	}
	
	public TermException(String message, Term term) {
		super(message);
		m_term = term;
	}
	
	/**
	 * @return the associated term
	 */
	public Term getTerm() {
		return m_term;
	}
	
	@Override
	public String toString() {
		if (m_term != null) {
			return super.toString() + " @term: " + m_term;
		} else {
			return super.toString();
		}
	}
}