/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This is an superclass of exceptions that occur when handling terms. It carries an error message as well as a term
 * instance.
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class TermException extends Exception {
	private static final long serialVersionUID = 628015504018345983L;

	public static final String UNKNOWN_VALUE_CLASS = "Unknown value class";
	public static final String UNKNOWN_TERM_STRUCTURE = "Unknown term structure";
	public static final String IS_NOT_IN_DNF = "Term is not in DNF";
	public static final String UNKNOWN_SORT_IN_EQUALITY = "Unknown sort in equality";
	public static final String EXPECTED_APPLICATION_TERM = "Expected application term";
	public static final String UNKNOWN_SUBCLASS_OF_TERM = "Stumbled upon a Term of unknown subclass";

	protected final Term mTerm;

	public TermException(final String message, final Term term) {
		super(message);
		mTerm = term;
	}

	/**
	 * @return the associated term
	 */
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public String toString() {
		if (mTerm != null) {
			return super.toString() + " @term: " + mTerm;
		}
		return super.toString();
	}
}
