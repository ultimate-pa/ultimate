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

import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


public class FlatApplicationTerm extends SharedTermOld {
	final FunctionSymbol m_Symbol;
	final SharedTermOld[] m_Parameters;
	SourceAnnotation m_SourceAnnotation;
	int hash;
	
	public FlatApplicationTerm(ConvertFormula converter, 
			FunctionSymbol sym, SharedTermOld[] args) {
		super(converter);
		m_Symbol = sym;
		m_Parameters = args;
	}
	
	public int hashCode() {
		if (hash == 0) {
			hash = m_Symbol.hashCode()*11 + Arrays.hashCode(m_Parameters);
			if (hash == 0)
				hash = 0x12345678;
		}
		return hash;
	}
	
	public boolean equals(Object o) {
		if (!(o instanceof FlatApplicationTerm))
			return false;
		FlatApplicationTerm appTerm = (FlatApplicationTerm) o;
		return m_Symbol == appTerm.m_Symbol
			&& Arrays.equals(m_Parameters, appTerm.m_Parameters);
	}
		
	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		Term[] params = new Term[m_Parameters.length];
		for (int i = 0; i < params.length; i++) { 
			params[i] = m_Parameters[i].getSMTTerm(useAuxVars);
		}
		return m_converter.getTheory().term(m_Symbol, params);
	}
	
	@Override
	public Sort getSort() {
		return m_Symbol.getReturnSort();
	}

	@Override
	public CCTerm toCCTerm() {
		if (m_ccterm == null) {
			CCTerm[] args = new CCTerm[m_Parameters.length];
			for (int i = 0; i < args.length; i++) {
				args[i] = m_Parameters[i].toCCTerm();
			}
//			m_ccterm = m_converter.cclosure.createFuncTerm(m_Symbol, args, this);
			if (m_converter.m_sourceAnnot != null)
				m_SourceAnnotation = (SourceAnnotation)
					((LeafNode)m_converter.m_sourceAnnot).getTheoryAnnotation(); 
			if (m_offset != null)
				share();
			m_converter.m_UnshareCC.add(this);
		}
		return m_ccterm;
	}
	
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		if (m_Parameters.length > 0) {
			sb.append("[").append(ctr).append("]");
			if (visited.contains(this))
				return;
			visited.add(this);
		}
		sb.append(m_Symbol.getName());
		if (m_Parameters.length == 0)
			return;
		String delim = "(";
		for (FlatTerm arg : m_Parameters) {
			sb.append(delim);
			arg.toStringHelper(sb, visited);
			delim = " ";
		}
		sb.append(")");
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}

	public FlatTerm[] getParameters() {
		return m_Parameters;
	}

	@Override
	public void unshareCC() {
		super.unshareCC();
		m_SourceAnnotation = null;
	}

	public SourceAnnotation getSourceAnnotation() {
		return m_SourceAnnotation;
	}
}
