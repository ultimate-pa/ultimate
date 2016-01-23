package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;

public class OctStatementProcessor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	
	private List<OctagonDomainState> mOldStates;
	private List<OctagonDomainState> mNewStates;
	
	public OctStatementProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
	}

	public List<OctagonDomainState> process(List<OctagonDomainState> oldStates, Statement statement) {
		mOldStates = oldStates;
		processStatement(statement);
		assert mNewStates != null && !mNewStates.isEmpty() : "Did not return any states";
		return mNewStates;
	}

	public void processStatement(Statement statement) {
		if (statement instanceof AssignmentStatement) {
			processAssignmentStatement((AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			processAssumeStatement((AssumeStatement) statement);
		} else if (statement instanceof HavocStatement) {
			processHavocStatement((HavocStatement) statement);
		} else if (statement instanceof IfStatement) {
			// TODO support
			throw new UnsupportedOperationException("IfStatements are currently not supported");
		} else if (statement instanceof Label) {
			// nothing to do
		} else {
			throw new UnsupportedOperationException("Unsupported type of statement: " + statement);
		}
	}

	private void processAssignmentStatement(AssignmentStatement statement) {
		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		assert lhs.length == rhs.length : "Unbalanced assignment: " + statement;
		int length = lhs.length;
				
		// TODO correct handling of "x, y := y, x;"
		if (lhs.length != 1) {
			throw new UnsupportedOperationException("parallel assignments are not supported yet");
		}
		
		for (int i = 0; i < length; ++i) {
			LeftHandSide l = lhs[i];
			if (l instanceof VariableLHS) {
				processSingleAssignment((VariableLHS) l, rhs[i]);
			}
			// else: Arrays and structs are assumed to be \top all the time
		}
		mNewStates = mOldStates;
	}
	
	private void processSingleAssignment(VariableLHS lhs, Expression rhs) {
		String var = lhs.getIdentifier();
		IType type = lhs.getType();
		if (TypeUtil.isBoolean(type)) {
			processBooleanAssign(var, rhs);
		} else if (TypeUtil.isNumeric(type)) {
			processNumericAssign(var, rhs);
		}
		// else: variables of unsupported types are assumed to be \top all the time
	}
	
	private void processBooleanAssign(String var, Expression rhs) {
		if (rhs instanceof BooleanLiteral) {
			mOldStates.forEach(s -> s.assignBooleanVar(var, BoolValue.get(((BooleanLiteral) rhs).getValue())));
		}
	}
	
	private void processNumericAssign(String var, Expression rhs) {
		 if (rhs instanceof IntegerLiteral) {
			assignNumericConstant(var, ((IntegerLiteral) rhs).getValue());
		} else if (rhs instanceof RealLiteral) {
			assignNumericConstant(var, ((RealLiteral) rhs).getValue());
		} else {
			mOldStates.forEach(s -> s.havocVar(var));
		}
//		if (rhs instanceof BinaryExpression) {
//			Expression beLhs = ((BinaryExpression) rhs).getLeft();
//			Expression beRhs = ((BinaryExpression) rhs).getRight();
//			// TODO
//		}
	}

	private void assignNumericConstant(String var, String numericConstant) {
		OctValue value = OctValue.parse(numericConstant);
		mOldStates.forEach(s -> s.assignNumericVarConstant(var, value));
	}

	private void processHavocStatement(HavocStatement statement) {
		for (OctagonDomainState oldState : mOldStates) {
			for (VariableLHS lhs : statement.getIdentifiers()) {
				oldState.havocVar(lhs.getIdentifier());
			}
		}
		mNewStates = mOldStates;
	}

	private void processAssumeStatement(AssumeStatement statement) {
		// TODO implement
		mNewStates = mOldStates; // note: returning old state is safe
	}
}
