package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxiliaryStatementContainer.StatementAssignment;

public class StateRecoverabilityAuxiliaryStatement implements AuxiliaryStatement {
	
	private PeaPhaseProgramCounter peaPhasePc;
	private String relatedVariable;
	private BoogieLocation loc;
	private String pcVariable;
	private int pc;
	private VerificationExpression verificationExpression;
	private Statement declVar;
	private Statement assignVar;
	private Statement ifSt;
	
	public StateRecoverabilityAuxiliaryStatement(String variable) {
		this.relatedVariable = variable;
	}
	
	public StateRecoverabilityAuxiliaryStatement(PeaPhaseProgramCounter peaPhasePc, String variable, String pcVariable, int pc, VerificationExpression ve) {
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

	public VerificationExpression getVerificationExpression() {
		return verificationExpression;
	}

	public void setVerificationExpression(VerificationExpression verificationExpression) {
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
