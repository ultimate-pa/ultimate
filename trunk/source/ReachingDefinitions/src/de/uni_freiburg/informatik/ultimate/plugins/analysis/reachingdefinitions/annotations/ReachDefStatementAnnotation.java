package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
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
		for (ScopedBoogieVar key : other.mDefs.keySet()) {
			for (IndexedStatement stmt : other.mDefs.get(key)) {
				rtr = addDef(key, stmt.getStatement(), stmt.getKey()) || rtr;
			}
		}
		return rtr;
	}

	@Override
	public ReachDefStatementAnnotation clone() {
		ReachDefStatementAnnotation rtr = new ReachDefStatementAnnotation();
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
