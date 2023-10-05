/*
 * Copyright (C) 2023 Tobias Wießner <tobias.wiessner@mailbox.org>
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxiliaryStatementContainer.StatementAssignment;

/**
*
* @author Tobias Wießner <tobias.wiessner@mailbox.org>
*
*/

public class AuxiliaryStatementContainer {
	public enum StatementAssignment {
		DECL_VAR, ASSIGN_VAR, IF_ST;
	}
	
	private Map<String, AuxiliaryStatement> mStatementMap;
	private Set<String> statements;
	
	public AuxiliaryStatementContainer() {
		mStatementMap = new HashMap<>();
	}
	
	public AuxiliaryStatementContainer(AuxiliaryStatementContainer auxStatement) {
		mStatementMap = auxStatement.getSreMap();
	}
	
	public List<Statement> getStatements(StatementAssignment stRecExpr) {
		List<Statement> statList = new ArrayList<>();
		for(AuxiliaryStatement auxStatement : mStatementMap.values()) {
			Statement s = auxStatement.getStatement(stRecExpr);
			if(s != null) {
				statList.add(s);
			}
		}
		return statList;
	}
	
	public Set<String> getRelatedVariableForInstance(Object object) {
		Set<String> relatedVariables = new HashSet<>();
		for(Map.Entry<String, AuxiliaryStatement> entry : mStatementMap.entrySet()) {
			if(entry.getValue().getClass().getName().equals(object.getClass().getName())) {
				relatedVariables.add(entry.getKey());
			}
		}
		return relatedVariables;
	}
	
	public Set<Statement> setBoogieLocationForInstance(Object object, StatementAssignment stRecExpr, final BoogieLocation bl) {
		Set<Statement> statements = new HashSet<>();
		for(Map.Entry<String, AuxiliaryStatement> entry : mStatementMap.entrySet()) {
			if(entry.getValue().getClass().getName().equals(object.getClass().getName())) {
				Statement statement = entry.getValue().getStatement(stRecExpr);
				if(statement != null) {
					statement.setLoc(bl);
				}
				statements.add(statement);
			}
		}
		return statements;
	}
	
	public AuxiliaryStatement addAuxStatement(String variable, AuxiliaryStatement auxStatement) {
		if(mStatementMap == null) {
			mStatementMap = new HashMap<>();
		}
		mStatementMap.put(variable, auxStatement);
		return auxStatement;
	}
	
	public Map<String, AuxiliaryStatement> getSreMap() {
		return mStatementMap;
	}

	public void setSreMap(Map<String, AuxiliaryStatement> sreMap) {
		this.mStatementMap = sreMap;
	}

	public Set<String> getStatements() {
		return statements;
	}

	public void setStatements(Set<String> statements) {
		this.statements = statements;
	}
}
