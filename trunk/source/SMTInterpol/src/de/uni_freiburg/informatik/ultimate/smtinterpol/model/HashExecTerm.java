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
		private final ExecTerm[] mArgs;
		private final int mHash;
		public Index(ExecTerm[] args) {
			mArgs = args;
			mHash = Arrays.hashCode(args);
		}
		public int hashCode() {
			return mHash;
		}
		public boolean equals(Object other) {
			if (other instanceof Index) {
				Index o = (Index) other;
				return Arrays.equals(mArgs, o.mArgs);
			}
			return false;
		}
		public Term toSMTLIB(Theory t, TermVariable[] vars) {
			assert(vars.length == mArgs.length);
			Term[] conj = new Term[vars.length];
			for (int i = 0; i < vars.length; ++i)
				conj[i] = t.equals(vars[i], ModelFormatter.toModelTerm(
						mArgs[i], null, t));
			return t.and(conj);
		}
	}
	
	private HashMap<Index, ExecTerm> mValues;
	private final ExecTerm mDefault;
	
	public HashExecTerm(ExecTerm defaultValue) {
		mDefault = defaultValue;
	}
	
	void extend(ExecTerm[] args, ExecTerm value) {
		if (mValues == null)
			mValues = new HashMap<Index, ExecTerm>();
		ExecTerm old = mValues.put(new Index(args), value);
		assert(old == null || old.equals(value));
	}

	@Override
	public ExecTerm evaluate(ExecTerm... args) {
		if (mValues == null)
			return mDefault;
		ExecTerm res = mValues.get(new Index(args));
		return res == null ? mDefault : res;
	}

	@Override
	public Term toSMTLIB(Theory t, TermVariable[] vars) {
		if (mValues == null)
			return mDefault.toSMTLIB(t, null);
		Term val = mDefault.toSMTLIB(t, null);
		for (Map.Entry<Index, ExecTerm> me : mValues.entrySet()) {
			// create (ite index value val)
			Term indexform = me.getKey().toSMTLIB(t, vars);
			val = t.ifthenelse(indexform, me.getValue().toSMTLIB(t, null), val);
		}
		return val;
	}
	
	Map<Index, ExecTerm> values() {
		return mValues;
	}
	
	ExecTerm getDefaultValue() {
		return mDefault;
	}

	@Override
	public boolean isUndefined() {
		return false;
	}

}
