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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

public class ModelFormatter {
	private final String mLineSep;
	private final StringBuilder mString;// NOPMD
	private int mIndent;

	private final Theory mTheory;

	private void newline() {
		mString.append(mLineSep);
		for (int i = 0; i < mIndent; ++i) {
			mString.append(' ');
		}
	}

	public ModelFormatter(final Theory t) {
		mLineSep = System.getProperty("line.separator");
		mString = new StringBuilder("(");// NOPMD
		mIndent = 0;
		mTheory = t;
	}

	public void appendComment(final String comment) {
		mIndent += Config.INDENTATION;
		newline();
		mString.append(";; ").append(comment);
		mIndent -= Config.INDENTATION;
	}

	public void appendSortInterpretation(final SortInterpretation si, final Sort sort) {
		final Term t = si.toSMTLIB(mTheory, sort);
		if (t != null) {
			mIndent += Config.INDENTATION;
			newline();
			mString.append(t);
			mIndent -= Config.INDENTATION;
		}
	}

	public void appendValue(final FunctionSymbol f, final TermVariable[] vars, final Term definition) {
		mIndent += Config.INDENTATION;
		newline();
		final Sort[] paramSorts = f.getParameterSorts();
		mString.append("(define-fun ").append(PrintTerm.quoteIdentifier(f.getName())).append(" (");
		for (int i = 0; i < vars.length; ++i) {
			mString.append('(').append(vars[i]).append(' ').append(paramSorts[i]).append(')');
		}
		mString.append(") ").append(f.getReturnSort());
		mIndent += Config.INDENTATION;
		appendFunctionValue(definition);
		mString.append(')');
		mIndent -= Config.INDENTATION;
		mIndent -= Config.INDENTATION;
	}

	private void appendFunctionValue(Term definition) {
		int closing = 0;
		while (definition instanceof ApplicationTerm
				&& ((ApplicationTerm) definition).getFunction().getName().equals(SMTLIBConstants.ITE)) {
			final Term[] iteArgs = ((ApplicationTerm) definition).getParameters();
			newline();
			mString.append("(ite ").append(iteArgs[0].toStringDirect()).append(' ').append(iteArgs[1].toStringDirect());
			definition = iteArgs[2];
			closing++;
		}
		if (closing > 0) {
			mIndent += Config.INDENTATION;
			newline();
			mString.append(definition.toStringDirect());
			for (int i = 0; i < closing; ++i) {
				mString.append(')');
			}
			mIndent -= Config.INDENTATION;
		} else {
			newline();
			mString.append(definition.toStringDirect());
		}
	}

	public String finish() {
		return mString.append(')').toString();
	}
}
