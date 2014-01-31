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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.IRAConstantFormatter;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.HashExecTerm.Index;

public class ModelFormatter {
	private final String mLineSep;
	private final StringBuilder mString;// NOPMD
	private int mIndent;
	
	private void newline() {
		mString.append(mLineSep);
		for (int i = 0; i < mIndent; ++i)
			mString.append(' ');
	}
	
	public ModelFormatter() {
		mLineSep = System.getProperty("line.separator");
		mString = new StringBuilder("(model ");// NOPMD
		mIndent = 0;
	}
	
	public void appendComment(String comment) {
		mIndent += Config.INDENTATION;
		newline();
		mString.append(";; ").append(comment);
		mIndent -= Config.INDENTATION;
	}
	
	public void appendSortInterpretation(
			SortInterpretation si, Sort sort, Theory t) {
		mIndent += Config.INDENTATION;
		newline();
		mString.append(si.toSMTLIB(t, sort));
		mIndent -= Config.INDENTATION;
	}
	
	public void appendValue(FunctionSymbol f, ExecTerm et, Theory t) {
		mIndent += Config.INDENTATION;
		newline();
		Sort[] paramSorts = f.getParameterSorts();
		TermVariable[] vars = new TermVariable[paramSorts.length];
		for (int i = 0; i < vars.length; ++i)
			vars[i] = t.createTermVariable("@" + i, paramSorts[i]);
		mString.append("(define-fun ").append(f.getName()).append(" (");
		for (int i = 0; i < vars.length; ++i)
			mString.append('(').append(vars[i]).append(' ').
				append(paramSorts[i]).append(')');
		mString.append(") ").append(f.getReturnSort());
		mIndent += Config.INDENTATION;
		appendExecTerm(et, vars, t);
		mString.append(')');
		mIndent -= Config.INDENTATION;
		mIndent -= Config.INDENTATION;
	}
	
	private void appendExecTerm(ExecTerm et, TermVariable[] vars, Theory t) {
		if (et instanceof Value) {
			newline();
			mString.append(toModelTerm(et, vars, t));
		} else if (et instanceof HashExecTerm) {
			HashExecTerm het = (HashExecTerm) et;
			Term defaultVal = toModelTerm(het.getDefaultValue(), null, t);
			int closing = 0;
			for (Map.Entry<Index, ExecTerm> me : het.values().entrySet()) {
				if (me.getValue() != defaultVal) {
					newline();
					mString.append("(ite ").append(
							me.getKey().toSMTLIB(t, vars)).append(' ').append(
									toModelTerm(me.getValue(), null, t));
					// We have to close one parenthesis;
					++closing;
				}
			}
			// Default value
			mIndent += Config.INDENTATION;
			newline();
			mString.append(defaultVal);
			for (int i = 0; i < closing; ++i)
				mString.append(')');
			mIndent -= Config.INDENTATION;
		} else
			throw new InternalError();
	}
	
	public String finish() {
		return mString.append(')').toString();
	}
	
	static Term toModelTerm(ExecTerm et, TermVariable[] vars, Theory t) {
		Term val = et.toSMTLIB(t, vars);
		return t.getLogic().isIRA() ? new IRAConstantFormatter().transform(val)
				: val;
	}
}
