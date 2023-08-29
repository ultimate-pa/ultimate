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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxiliaryStatementContainer.StatementAssignment;

/**
*
* @author Tobias Wießner <tobias.wiessner@mailbox.org>
*
*/

public class StateRecoverabilityAuxiliaryStatement implements AuxiliaryStatement {
	
	private PeaPhaseProgramCounter peaPhasePc;
	private String relatedVariable;
	private BoogieLocation loc;
	private String pcVariable;
	private int pc;
	private StateRecoverabilityVerificationCondition verificationExpression;
	private Statement declVar;
	private Statement assignVar;
	private Statement ifSt;
	
	public StateRecoverabilityAuxiliaryStatement(String variable) {
		this.relatedVariable = variable;
	}
	
	public StateRecoverabilityAuxiliaryStatement(PeaPhaseProgramCounter peaPhasePc, String variable, String pcVariable, int pc, StateRecoverabilityVerificationCondition ve) {
		this.peaPhasePc = peaPhasePc;
		this.relatedVariable = variable;
		this.pcVariable = pcVariable;
		this.pc = pc;
		this.verificationExpression = ve;
	}

	@Override
	public Statement getStatement(StatementAssignment stRecExpr) {
		Statement s = null;
		switch (stRecExpr) {
		case DECL_VAR:
			return this.getDeclVar();
		case ASSIGN_VAR:
			return this.getAssignVar();
		case IF_ST:
			return this.getIfSt();
		default:
			break;
		}
		return null;
	}

	public String getRelatedVariable() {
		return relatedVariable;
	}

	public void setRelatedVariable(String relatedVariable) {
		this.relatedVariable = relatedVariable;
	}

	public String getPcVariable() {
		return pcVariable;
	}

	public void setPcVariable(String pcVariable) {
		this.pcVariable = pcVariable;
	}

	public int getPc() {
		return pc;
	}

	public void setPc(int pc) {
		this.pc = pc;
	}

	public StateRecoverabilityVerificationCondition getVerificationExpression() {
		return verificationExpression;
	}

	public void setVerificationExpression(StateRecoverabilityVerificationCondition verificationExpression) {
		this.verificationExpression = verificationExpression;
	}

	public Statement getDeclVar() {
		return declVar;
	}

	public void setDeclVar(Statement declVar) {
		this.declVar = declVar;
	}

	public Statement getAssignVar() {
		return assignVar;
	}

	public void setAssignVar(Statement assignVar) {
		this.assignVar = assignVar;
	}

	public Statement getIfSt() {
		return ifSt;
	}

	public void setIfSt(Statement ifSt) {
		this.ifSt = ifSt;
	}
	
	public PeaPhaseProgramCounter getPeaPhasePc() {
		return peaPhasePc;
	}

	public void setPeaPhasePc(PeaPhaseProgramCounter peaPhasePc) {
		this.peaPhasePc = peaPhasePc;
	}

	@Override
	public BoogieLocation setBoogieLocation(BoogieLocation loc) {
		this.loc = loc;
		return loc;
	}

	@Override
	public BoogieLocation getBoogieLocation() {
		return this.loc;
	}
}
