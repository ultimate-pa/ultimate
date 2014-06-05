package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class ReachingDefinitionsStatementAnnotation extends ReachingDefinitionsBaseAnnotation {

	private static final long serialVersionUID = 1L;

	HashMap<String, HashSet<Statement>> mDefs;
	HashMap<String, HashSet<Statement>> mUse;

	public ReachingDefinitionsStatementAnnotation() {
		mDefs = new HashMap<>();
		mUse = new HashMap<>();
	}

	public void removeAllDefs(String variableName) {
		mDefs.remove(variableName);
	}

	public boolean addDef(String variableName, Statement stmt) {
		HashSet<Statement> rtr = mDefs.get(variableName);
		if (rtr == null) {
			rtr = new HashSet<>();
			mDefs.put(variableName, rtr);

		}
		return rtr.add(stmt);
	}

	public boolean addUse(String variableName, Statement stmt) {
		HashSet<Statement> rtr = mUse.get(variableName);
		if (rtr == null) {
			rtr = new HashSet<>();
			mUse.put(variableName, rtr);
		}

		return rtr.add(stmt);
	}

	/**
	 * 
	 * @param other
	 * @return true iff this Def set was changed.
	 */
	public boolean unionDef(ReachingDefinitionsStatementAnnotation other) {
		if (other.mDefs == null) {
			return false;
		}

		boolean rtr = false;
		for (String key : other.mDefs.keySet()) {
			for (Statement stmt : other.mDefs.get(key)) {
				rtr = addDef(key, stmt) || rtr;
			}
		}
		return rtr;
	}

	public ReachingDefinitionsStatementAnnotation copy() {
		ReachingDefinitionsStatementAnnotation rtr = new ReachingDefinitionsStatementAnnotation();
		if (mDefs != null) {
			rtr.mDefs = new HashMap<>(mDefs);
		}
		
		if(mUse != null){
			rtr.mUse = new HashMap<>(mUse);
		}
		
		return rtr;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getDefs() {
		return mDefs;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getUse() {
		return mUse;
	}

}
