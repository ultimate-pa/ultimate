package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class ReachDefStatementAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private HashMap<String, HashSet<Statement>> mDefs;
	private HashMap<String, HashSet<Statement>> mUse;

	public ReachDefStatementAnnotation() {
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
	
	public Collection<Statement> getDef(String variableName){
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
		for (String key : other.mDefs.keySet()) {
			for (Statement stmt : other.mDefs.get(key)) {
				rtr = addDef(key, stmt) || rtr;
			}
		}
		return rtr;
	}

	@Override
	public ReachDefBaseAnnotation clone() {
		ReachDefStatementAnnotation rtr = new ReachDefStatementAnnotation();
		rtr.mDefs = copy(mDefs);
		rtr.mUse = copy(mUse);

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
