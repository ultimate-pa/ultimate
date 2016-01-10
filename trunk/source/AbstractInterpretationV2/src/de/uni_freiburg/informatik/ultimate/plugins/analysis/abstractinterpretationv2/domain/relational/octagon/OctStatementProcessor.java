package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class OctStatementProcessor extends BoogieVisitor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	
	private OctagonDomainState mOldState;
	private OctagonDomainState mNewState;
	private List<OctagonDomainState> mNewStates;
	
	public OctStatementProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
	}

	public List<OctagonDomainState> process(OctagonDomainState oldState, Statement statement) {
		mOldState = oldState;
		mNewStates = new ArrayList<>();
		processStatement(statement);
		return mNewStates;
	}

	@Override
	protected Statement processStatement(Statement statement) {
		mNewState = mOldState.deepCopy();
		boolean consumed = false;
		if (statement instanceof AssignmentStatement) {
			processAssignmentStatement((AssignmentStatement) statement);
			consumed = true;
		} else if (statement instanceof AssumeStatement) {
			processAssumeStatement((AssumeStatement) statement);
			consumed = true;
		} else if (statement instanceof HavocStatement) {
			processHavocStatement((HavocStatement) statement);
			consumed = true;
		}
		if (consumed) {
			mNewStates.add(mNewState);
			return statement;
		}
		return super.processStatement(statement);
	}

	private void processAssignmentStatement(AssignmentStatement statement) {
		
		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		assert lhs.length == rhs.length;
		int length = lhs.length;
		for (int i = 0; i < length; ++i) {
			LeftHandSide l = lhs[i];
			if (l instanceof VariableLHS) {
				processSingleAssignment((VariableLHS) l, rhs[i]);
			}
			// else: Arrays and structs are assumed to be \top all the time
		}
		
	}
	
	private void processSingleAssignment(VariableLHS lhs, Expression rhs) {
		String var = lhs.getIdentifier();
		IType type = lhs.getType();
		if (OctagonDomainState.isBoolean(type)) {
			processBooleanAssign(var, rhs);
		} else if (OctagonDomainState.isNumeric(type)) {
			processNumericAssign(var, rhs);
		}
		// else: variables of unsupported types are assumed to be \top all the time
	}
	
	private void processBooleanAssign(String var, Expression rhs) {
		if (rhs instanceof BooleanLiteral) {
			mNewState.assignBooleanVar(var, BoolValue.get(((BooleanLiteral) rhs).getValue()));
		}
	}
	
	private void processNumericAssign(String var, Expression rhs) {
		 if (rhs instanceof IntegerLiteral) {
			assignNumericConstant(var, ((IntegerLiteral) rhs).getValue());
		} else if (rhs instanceof RealLiteral) {
			assignNumericConstant(var, ((RealLiteral) rhs).getValue());
		} else {
			mNewState.havocVar(var);
		}
//		if (rhs instanceof BinaryExpression) {
//			Expression beLhs = ((BinaryExpression) rhs).getLeft();
//			Expression beRhs = ((BinaryExpression) rhs).getRight();
//			// TODO
//		}
	}

	private void assignNumericConstant(String var, String numericConstant) {
		OctValue value = OctValue.parse(numericConstant);
		mNewState.assignNumericVarConstant(var, value);
	}

	private void processHavocStatement(HavocStatement statement) {
		// TODO implement
	}

	private void processAssumeStatement(AssumeStatement statement) {
		// TODO implement
		// note: returning old state is safe
	}
}
