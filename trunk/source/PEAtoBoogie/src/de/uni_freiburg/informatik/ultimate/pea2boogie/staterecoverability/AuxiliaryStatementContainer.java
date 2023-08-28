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
