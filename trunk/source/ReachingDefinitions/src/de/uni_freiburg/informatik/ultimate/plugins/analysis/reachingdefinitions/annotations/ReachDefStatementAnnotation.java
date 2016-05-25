/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;

public class ReachDefStatementAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> mDefs;
	private HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> mUse;

	public ReachDefStatementAnnotation() {
		mDefs = new HashMap<>();
		mUse = new HashMap<>();
	}

	public void removeAllDefs(ScopedBoogieVar variable) {
		mDefs.remove(variable);
	}

	// public boolean addDef(ScopedBoogieVar variable, Statement stmt) {
	// return addDef(variable, stmt, null);
	// }

	public boolean addDef(ScopedBoogieVar variable, Statement stmt, String key) {
		HashSet<IndexedStatement> rtr = mDefs.get(variable);
		if (rtr == null) {
			rtr = new HashSet<>();
			mDefs.put(variable, rtr);
		}
		return rtr.add(new IndexedStatement(stmt, key));
	}

	public boolean addUse(ScopedBoogieVar variable, Statement stmt, String key) {
		HashSet<IndexedStatement> rtr = mUse.get(variable);
		if (rtr == null) {
			rtr = new HashSet<>();
			mUse.put(variable, rtr);
		}

		return rtr.add(new IndexedStatement(stmt, key));
	}

	public Collection<IndexedStatement> getDef(ScopedBoogieVar variableName) {
		return getDefs().get(variableName);
	}

	/**
	 * 
	 * @param other
	 * @return true iff this Def set was changed.
	 */
	public boolean unionDef(ReachDefStatementAnnotation other) {
		if (other.mDefs == null) {
			return false;
		}

		if (other == this) {
			return false;
		}

		boolean rtr = false;
		for (final ScopedBoogieVar key : other.mDefs.keySet()) {
			for (final IndexedStatement stmt : other.mDefs.get(key)) {
				rtr = addDef(key, stmt.getStatement(), stmt.getKey()) || rtr;
			}
		}
		return rtr;
	}

	@Override
	public ReachDefStatementAnnotation clone() {
		final ReachDefStatementAnnotation rtr = new ReachDefStatementAnnotation();
		rtr.mDefs = copy(mDefs);
		rtr.mUse = copy(mUse);

		return rtr;
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getDefs() {
		return mDefs;
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getUse() {
		return mUse;
	}

}
