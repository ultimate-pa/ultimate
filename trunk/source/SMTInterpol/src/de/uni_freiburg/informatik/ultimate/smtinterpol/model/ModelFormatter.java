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

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue.Index;

public class ModelFormatter {
	private final String mLineSep;
	private final StringBuilder mString;// NOPMD
	private int mIndent;

	private final Theory mTheory;
	private final Model mModel;

	private void newline() {
		mString.append(mLineSep);
		for (int i = 0; i < mIndent; ++i) {
			mString.append(' ');
		}
	}

	public ModelFormatter(final Theory t, final Model model) {
		mLineSep = System.getProperty("line.separator");
		mString = new StringBuilder("(model ");// NOPMD
		mIndent = 0;
		mTheory = t;
		mModel = model;
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

	public void appendValue(final FunctionSymbol f, final FunctionValue value, final Theory t) {
		mIndent += Config.INDENTATION;
		newline();
		final Sort[] paramSorts = f.getParameterSorts();
		final TermVariable[] vars = new TermVariable[paramSorts.length];
		for (int i = 0; i < vars.length; ++i) {
			vars[i] = t.createTermVariable("@p" + i, paramSorts[i]);
		}
		mString.append("(define-fun ").append(PrintTerm.quoteIdentifier(f.getName())).append(" (");
		for (int i = 0; i < vars.length; ++i) {
			mString.append('(').append(vars[i]).append(' ').append(paramSorts[i]).append(')');
		}
		mString.append(") ").append(f.getReturnSort());
		mIndent += Config.INDENTATION;
		appendFunctionValue(value, vars, f.getReturnSort());
		mString.append(')');
		mIndent -= Config.INDENTATION;
		mIndent -= Config.INDENTATION;
	}

	private void appendFunctionValue(final FunctionValue value, final TermVariable[] vars, final Sort resultSort) {
		if (vars.length == 0) {
			newline();
			mString.append(mModel.toModelTerm(value.getDefault(), resultSort).toStringDirect());
		} else {
			final int defaultVal = value.getDefault();
			int closing = 0;
			for (final Entry<Index, Integer> me : value.values().entrySet()) {
				if (me.getValue() != defaultVal) {
					newline();
					mString.append("(ite ").append(mModel.index2Term(me.getKey(), vars).toStringDirect()).append(' ')
							.append(mModel.toModelTerm(me.getValue(), resultSort).toStringDirect());
					// We have to close one parenthesis;
					++closing;
				}
			}
			// Default value
			mIndent += Config.INDENTATION;
			newline();
			mString.append(mModel.toModelTerm(defaultVal, resultSort).toStringDirect());
			for (int i = 0; i < closing; ++i) {
				mString.append(')');
			}
			mIndent -= Config.INDENTATION;
		}
	}

	public String finish() {
		return mString.append(')').toString();
	}

}
