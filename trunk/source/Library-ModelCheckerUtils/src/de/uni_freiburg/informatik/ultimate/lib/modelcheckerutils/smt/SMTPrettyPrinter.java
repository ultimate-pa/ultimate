/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Static class for pretty-printing SMT formulae
 * 
 * @author Jan Leike 
 * @author Matthias Heizmann
 */
public class SMTPrettyPrinter {
	private static final String s_indentation = "    ";
	private static final String[] s_infix_functions =
		{"+", "-", "*", "/", "=", ">=", "<=", ">", "<"};
	
	private final Term mTerm;
	
	public SMTPrettyPrinter(final Term term) {
		mTerm = term;
	}
	
	private static void indent(final StringBuilder sb, final int indentation) {
		for (int i = 0; i < indentation; ++i) {
			sb.append(s_indentation);
		}
	}
	
	/**
	 * Convert an SMT term into a more human readable format
	 * 
	 * @param term an SMT term
	 * @return a human-readable representation of the term
	 */
	private static String print(final Term term, final int indentation) {
		assert(indentation >= 0);
		
		final StringBuilder sb = new StringBuilder();
		if (term instanceof ConstantTerm) {
			return term.toString();
		} else if (term instanceof TermVariable) {
			return term.toString();
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appt = (ApplicationTerm) term;
			final String fname = appt.getFunction().getName();
			
			if (appt.getParameters().length == 0) {
				return fname;
			}
			if (fname.equals("ite")) {
				sb.append("(");
				sb.append(print(appt.getParameters()[0], indentation + 1));
				sb.append(" ? ");
				sb.append(print(appt.getParameters()[1], indentation + 1));
				sb.append(" : ");
				sb.append(print(appt.getParameters()[2], indentation + 1));
				sb.append(")");
				return sb.toString();
			}
			
			// Recursively convert parameters
			sb.append("(");
			boolean infix = false;
			for (final String infix_fname : s_infix_functions) {
				if (fname.equals(infix_fname)) {
					infix = true; // write the function symbol in infix notation
				}
			}
			if (appt.getParameters().length == 1) {
				sb.append(fname);
				sb.append(" ");
				sb.append(print(appt.getParameters()[0],0));
				sb.append(")");
				return sb.toString();
			} else if (!infix) {
				sb.append(fname);
				sb.append("\n");
			}
			for (int i = 0; i < appt.getParameters().length; ++i) {
				if (infix) {
					if (i > 0) {
						sb.append(" ");
						sb.append(fname);
						sb.append(" ");
					}
				} else {
					indent(sb, indentation + 1);
				}
				sb.append(print(appt.getParameters()[i], indentation + 1));
				if (!infix) {
					sb.append("\n");
				}
			}
			if (!infix) {
				indent(sb, indentation);
			}
			sb.append(")");
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annot = (AnnotatedTerm) term;
			for (final Annotation a : annot.getAnnotations()) {
				indent(sb, indentation);
				sb.append("{");
				sb.append(a.getKey());
				sb.append(" ");
				sb.append(a.getValue());
				sb.append("}\n");
			}
			sb.append(print(annot.getSubterm(), indentation));
		} else {
			assert(false); // Not implemented
		}
		return sb.toString();
	}
	

	@Override
	public String toString() {
		return print(mTerm, 0);
	}
}
