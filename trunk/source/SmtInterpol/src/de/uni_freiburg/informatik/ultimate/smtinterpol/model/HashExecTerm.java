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

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Representation of a function the is equal to a default value except for
 * finitely many positions.
 * @author Juergen Christ
 */
public class HashExecTerm implements ExecTerm {
	
	static class Index {
		private Term[] m_Args;
		private int m_Hash;
		public Index(Term[] args) {
			m_Args = args;
			m_Hash = Arrays.hashCode(args);
		}
		public int hashCode() {
			return m_Hash;
		}
		public boolean equals(Object other) {
			if (other instanceof Index) {
				Index o = (Index) other;
				return Arrays.equals(m_Args, o.m_Args);
			}
			return false;
		}
		public Term toSMTLIB(Theory t, TermVariable[] vars) {
			assert(vars.length == m_Args.length);
			Term[] conj = new Term[vars.length];
			for (int i = 0; i < vars.length; ++i)
				conj[i] = t.equals(vars[i], m_Args[i]);
			return t.and(conj);
		}
	}
	
	private HashMap<Index, Term> m_Values;
	private Term m_Default;
	
	public HashExecTerm(Term defaultValue) {
		m_Default = defaultValue;
	}
	
	void extend(Term[] args, Term value) {
		if (m_Values == null)
			m_Values = new HashMap<Index, Term>();
		Term old = m_Values.put(new Index(args), value);
		assert(old == null || old == value);
	}

	@Override
	public Term evaluate(Term... args) {
		if (m_Values == null)
			return m_Default;
		Term res = m_Values.get(new Index(args));
		return res != null ? res : m_Default;
	}

	@Override
	public Term toSMTLIB(Theory t, TermVariable[] vars) {
		if (m_Values == null)
			return m_Default;
		Term val = m_Default;
		for (Map.Entry<Index, Term> me : m_Values.entrySet()) {
			// create (ite index value val)
			Term indexform = me.getKey().toSMTLIB(t, vars);
			val = t.ifthenelse(indexform, me.getValue(), val);
		}
		return val;
	}
	
	Map<Index, Term> values() {
		return m_Values;
	}
	
	Term getDefaultValue() {
		return m_Default;
	}

}
