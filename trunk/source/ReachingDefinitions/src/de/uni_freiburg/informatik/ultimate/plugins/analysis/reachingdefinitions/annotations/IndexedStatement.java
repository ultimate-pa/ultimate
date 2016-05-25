/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;

public class IndexedStatement {

	private final Statement mStatement;
	private final String mKey;

	public IndexedStatement(Statement stmt, String key) {
		mStatement = stmt;
		mKey = key;
	}

	public Statement getStatement() {
		return mStatement;
	}

	public String getKey() {
		return mKey;
	}

	@Override
	public String toString() {
		return "[" + mKey + "]: " + mStatement.hashCode() + " " + BoogiePrettyPrinter.print(mStatement);
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
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final IndexedStatement other = (IndexedStatement) obj;
		if (mKey == null) {
			if (other.mKey != null) {
				return false;
			}
		} else if (!mKey.equals(other.mKey)) {
			return false;
		}
		if (mStatement == null) {
			if (other.mStatement != null) {
				return false;
			}
		} else if (!mStatement.equals(other.mStatement)) {
			return false;
		}
		return true;
	}

}
