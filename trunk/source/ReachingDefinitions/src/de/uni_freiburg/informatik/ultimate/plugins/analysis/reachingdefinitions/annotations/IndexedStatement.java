package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class IndexedStatement {

	private final Statement mStatement;
	private final String mKey;

	public IndexedStatement(Statement stmt, String key) {
		mStatement = stmt;
		mKey = key;
	}
	
	public Statement getStatement(){
		return mStatement;
	}
	
	public String getKey(){
		return mKey;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mKey == null) ? 0 : mKey.hashCode());
		result = prime * result + ((mStatement == null) ? 0 : mStatement.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		IndexedStatement other = (IndexedStatement) obj;
		if (mKey == null) {
			if (other.mKey != null)
				return false;
		} else if (!mKey.equals(other.mKey))
			return false;
		if (mStatement == null) {
			if (other.mStatement != null)
				return false;
		} else if (!mStatement.equals(other.mStatement))
			return false;
		return true;
	}
	
}
