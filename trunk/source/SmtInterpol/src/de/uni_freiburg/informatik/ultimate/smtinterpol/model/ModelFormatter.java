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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.HashExecTerm.Index;

public class ModelFormatter {
	private String m_LineSep;
	private StringBuilder m_String;
	private int m_Indent;
	
	private void newline() {
		m_String.append(m_LineSep);
		for (int i = 0; i < m_Indent; ++i)
			m_String.append(' ');
	}
	
	public ModelFormatter() {
		m_LineSep = System.getProperty("line.separator");
		m_String = new StringBuilder("(model ");
		m_Indent = 0;
	}
	
	public void appendComment(String comment) {
		m_Indent += Config.INDENTATION;
		newline();
		m_String.append(";; ").append(comment);
		m_Indent -= Config.INDENTATION;
	}
	
	public void appendSortInterpretation(
			SortInterpretation si, Sort sort, Theory t) {
		m_Indent += Config.INDENTATION;
		newline();
		m_String.append(si.toSMTLIB(t, sort));
		m_Indent -= Config.INDENTATION;
	}
	
	public void appendValue(FunctionSymbol f, ExecTerm et, Theory t) {
		m_Indent += Config.INDENTATION;
		newline();
		TermVariable[] vars = new TermVariable[f.getParameterCount()];
		for (int i = 0; i < vars.length; ++i)
			vars[i] = t.createTermVariable("@" + i, f.getParameterSort(i));
		m_String.append("(define-fun ").append(f.getName()).append(" (");
		for (int i = 0; i < vars.length; ++i)
			m_String.append('(').append(vars[i]).append(' ').
				append(f.getParameterSort(i)).append(')');
		m_String.append(") ").append(f.getReturnSort());
		m_Indent += Config.INDENTATION;
		appendExecTerm(et, vars, t);
		m_String.append(')');
		m_Indent -= Config.INDENTATION;
		m_Indent -= Config.INDENTATION;
	}
	
	private void appendExecTerm(ExecTerm et, TermVariable[] vars, Theory t) {
		if (et instanceof Value) {
			newline();
			m_String.append(et.toSMTLIB(t, vars));
		}
		else if (et instanceof HashExecTerm) {
			HashExecTerm het = (HashExecTerm) et;
			Term defaultVal = het.getDefaultValue();
			int closing = 0;
			for (Map.Entry<Index, Term> me : het.values().entrySet()) {
				if (me.getValue() != defaultVal) {
					newline();
					m_String.append("(ite ").append(
							me.getKey().toSMTLIB(t, vars)).append(' ').append(
									me.getValue());
					// We have to close one parenthesis;
					++closing;
				}
			}
			// Default value
			m_Indent += Config.INDENTATION;
			newline();
			m_String.append(defaultVal);
			for (int i = 0; i < closing; ++i)
				m_String.append(')');
			m_Indent -= Config.INDENTATION;
		} else
			throw new InternalError();
	}
	
	public String finish() {
		return m_String.append(')').toString();
	}
	
	
}
