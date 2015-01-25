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
import de.uni_freiburg.informatik.ultimate.logic.IRAConstantFormatter;
import de.uni_freiburg.informatik.ultimate.logic.Identifier;
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
	
	private final IRAConstantFormatter mFormatter;
	
	private void newline() {
		mString.append(mLineSep);
		for (int i = 0; i < mIndent; ++i)
			mString.append(' ');
	}
	
	public ModelFormatter(Theory t, Model model) {
		mLineSep = System.getProperty("line.separator");
		mString = new StringBuilder("(model ");// NOPMD
		mIndent = 0;
		mTheory = t;
		mModel = model;
		mFormatter = t.getLogic().isIRA() ? new IRAConstantFormatter() : null;
	}
	
	public void appendComment(String comment) {
		mIndent += Config.INDENTATION;
		newline();
		mString.append(";; ").append(comment);
		mIndent -= Config.INDENTATION;
	}
	
	public void appendSortInterpretation(
			SortInterpretation si, Sort sort) {
		Term t = si.toSMTLIB(mTheory, sort);
		if (t != null) {
			mIndent += Config.INDENTATION;
			newline();
			mString.append(t);
			mIndent -= Config.INDENTATION;
		}
	}
	
	public void appendValue(FunctionSymbol f, FunctionValue value, Theory t) {
		mIndent += Config.INDENTATION;
		newline();
		Sort[] paramSorts = f.getParameterSorts();
		TermVariable[] vars = new TermVariable[paramSorts.length];
		for (int i = 0; i < vars.length; ++i)
			vars[i] = t.createTermVariable("@p" + i, paramSorts[i]);
		mString.append("(define-fun ").append(Identifier.quoteIdentifier(
				f.getName())).append(" (");
		for (int i = 0; i < vars.length; ++i)
			mString.append('(').append(vars[i]).append(' ').
				append(paramSorts[i]).append(')');
		mString.append(") ").append(f.getReturnSort());
		mIndent += Config.INDENTATION;
		appendFunctionValue(value, vars, f.getReturnSort());
		mString.append(')');
		mIndent -= Config.INDENTATION;
		mIndent -= Config.INDENTATION;
	}
	
	private Term index2Term(Index index, TermVariable[] vars) {
		int[] idx = index.getArray();
		assert vars.length == idx.length;
		Term[] conj = new Term[vars.length];
		for (int i = 0; i < vars.length; ++i)
			conj[i] = mTheory.equals(vars[i],
					mModel.toModelTerm(idx[i], vars[i].getSort()));
		return mTheory.and(conj);
	}
	
	private void appendFunctionValue(FunctionValue value, TermVariable[] vars,
			Sort resultSort) {
		if (vars.length == 0) {
			newline();
			mString.append(format(
					mModel.toModelTerm(value.getDefault(), resultSort))
					.toStringDirect());
		} else {
			int defaultVal = value.getDefault();
			int closing = 0;
			for (Entry<Index, Integer> me : value.values().entrySet()) {
				if (me.getValue() != defaultVal) {
					newline();
					mString.append("(ite ").append(
							format(index2Term(me.getKey(), vars))
							.toStringDirect()).append(' ')
							.append(format(
									mModel.toModelTerm(
											me.getValue(), resultSort))
											.toStringDirect());
					// We have to close one parenthesis;
					++closing;
				}
			}
			// Default value
			mIndent += Config.INDENTATION;
			newline();
			mString.append(format(mModel.toModelTerm(defaultVal, resultSort))
					.toStringDirect());
			for (int i = 0; i < closing; ++i)
				mString.append(')');
			mIndent -= Config.INDENTATION;
		}
	}
	
	private Term format(Term input) {
		return mFormatter == null ? input : mFormatter.transform(input);
	}

	public String finish() {
		return mString.append(')').toString();
	}
	
}
