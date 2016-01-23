package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieAstUtil;
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
		if (length == 1) {
			LeftHandSide l = lhs[0];
			if (l instanceof VariableLHS) {
				processSingleAssignment(((VariableLHS) l).getIdentifier(), rhs[0]);
			}
			// else: Arrays and structs are assumed to be \top all the time
			
		} else {
			Map<String, IBoogieVar> tmpVars = new HashMap<>();
			Map<String, String> mapTmpVarToOrigVar = new HashMap<>();
			Map<String, Expression> mapLhsToRhs = new HashMap<>();
			for (int i = 0; i < length; ++i) {
				LeftHandSide l = lhs[i];
				if (l instanceof VariableLHS) {
					VariableLHS vl = (VariableLHS) l;
					// parentheses are not allowed in Boogie-identifiers => tmpVar is unique
					String tmpVar = "octTmp(" + vl.getIdentifier() + ")"; 
					tmpVars.put(tmpVar, BoogieAstUtil.createTemporaryIBoogieVar(tmpVar, vl.getType()));
					mapLhsToRhs.put(tmpVar, rhs[i]);
				}
				// else: variables of unsupported types are assumed to be \top all the time
			}
			// add temporary variables
			mNewStates = new ArrayList<>(mOldStates.size());
			mOldStates.forEach(oldState -> mNewStates.add(oldState.addVariables(tmpVars)));
			
			// (tmpVar := origExpr)*
			mOldStates = mNewStates;
			mapLhsToRhs.entrySet().forEach(entry -> processSingleAssignment(entry.getKey(), entry.getValue()));
			
			// (origVar := tmpVar)*
			mOldStates = mNewStates;
			mOldStates.forEach(oldState -> oldState.assignVars(mapTmpVarToOrigVar));
			mNewStates = mOldStates;

			// TODO remove duplicated states (may occur due to assignments)

			// remove temporary variables
			mOldStates = mNewStates;
			mNewStates = new ArrayList<>(mOldStates.size());
			mOldStates.forEach(s -> mNewStates.add(s.removeVariables(tmpVars)));
		}
	}
	
	private void processSingleAssignment(String lhsVar, Expression rhs) {
		IType type = rhs.getType(); // note: there is no implicit typecasting in boogie. "real := int;" cannot happen. 
		if (TypeUtil.isBoolean(type)) {
			processBooleanAssign(lhsVar, rhs);
		} else if (TypeUtil.isNumeric(type)) {
			processNumericAssign(lhsVar, rhs);
		}
		// else: variables of unsupported types are assumed to be \top all the time
		mNewStates = mOldStates;
	}
	
	private void processBooleanAssign(String var, Expression rhs) {
		if (rhs instanceof BooleanLiteral) {
			BoolValue value = BoolValue.get(((BooleanLiteral) rhs).getValue());
			mOldStates.forEach(s -> s.assignBooleanVar(var, value));
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
		// TODO use AffineExpression to assign relations
		// TODO project vars to intervals and calculate (if not affine)
//		if (rhs instanceof BinaryExpression) {
//			Expression beLhs = ((BinaryExpression) rhs).getLeft();
//			Expression beRhs = ((BinaryExpression) rhs).getRight();
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
