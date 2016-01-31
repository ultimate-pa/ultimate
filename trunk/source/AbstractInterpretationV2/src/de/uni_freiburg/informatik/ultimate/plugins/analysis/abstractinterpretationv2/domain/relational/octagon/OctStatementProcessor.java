package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieAstUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class OctStatementProcessor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	
	private final ExpressionTransformer mExprTransformer = new ExpressionTransformer();
	
	/**
	 * Abstract domain states before the interpretation of an statement.
	 * Interpretation of statements should happen for each of these states separately.
	 * <p>
	 * Most methods of this class use the attribute as an input.
	 * Methods may also modify the list or even the states inside the list!
	 */
	private List<OctagonDomainState> mOldStates;
	
	/**
	 * Abstract domain states after the interpretation of an statement.
	 * After interpreting an statement, there may be more states than before due to splitting.
	 * Example: {@code assume x != 0} can be split into {@code assume x < 0} and {@code assume x > 0}.
	 * <p>
	 * Methods of this class use the attribute as an output.
	 */
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

	private void processStatement(Statement statement) {
		if (statement instanceof AssignmentStatement) {
			processAssignmentStatement((AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			processAssumeStatement(((AssumeStatement) statement).getFormula());
		} else if (statement instanceof HavocStatement) {
			processHavocStatement((HavocStatement) statement);
		} else if (statement instanceof IfStatement) {
			// TODO support if it can occur
			String msg = "IfStatements are not supported by post-operator. Switch block-encoding to single statements.";
			throw new UnsupportedOperationException(msg);
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
			assert l.getType().equals(rhs[0].getType()) : "Assignment with incompatible types";
			if (l instanceof VariableLHS) {
				processSingleAssignment(((VariableLHS) l).getIdentifier(), rhs[0]);
			}
			// else: variables of unsupported types are assumed to be \top all the time
		} else {
			Map<String, IBoogieVar> tmpVars = new HashMap<>();
			Map<String, String> mapTmpVarToOrigVar = new HashMap<>();
			Map<String, Expression> mapLhsToRhs = new HashMap<>();
			for (int i = 0; i < length; ++i) {
				LeftHandSide l = lhs[i];
				assert l.getType().equals(rhs[i].getType()) : "Assignment with incompatible types";
				if (l instanceof VariableLHS) {
					VariableLHS vLhs = (VariableLHS) l;
					String origVar = vLhs.getIdentifier();
					// parentheses are not allowed in Boogie-identifiers => tmpVar is unique
					String tmpVar = "octTmp(" + origVar + ")"; 
					tmpVars.put(tmpVar, BoogieAstUtil.createTemporaryIBoogieVar(tmpVar, vLhs.getType()));
					mapTmpVarToOrigVar.put(tmpVar, origVar);
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
			mOldStates.forEach(oldState -> oldState.copyVars(mapTmpVarToOrigVar));
			mNewStates = mOldStates;

			// remove temporary variables
			mOldStates = mNewStates;
			mNewStates = new ArrayList<>(mOldStates.size());
			mOldStates.forEach(s -> mNewStates.add(s.removeVariables(tmpVars)));
		}

		// TODO remove duplicated states (may occur due to assignments)
	}
	
	private void processSingleAssignment(String targetVar, Expression rhs) {
		List<Pair<List<Expression>, Expression>> paths = mExprTransformer.removeIfExprsCached(rhs);
		List<OctagonDomainState> tmpNewStates = new ArrayList<>();
		for (Pair<List<Expression>, Expression> p : paths) {
			// !!!!!!!!!!!!!!! 
			// TODO !!!!!!!!!!  processAssume may modify mOldStates => Copy or ensure that this never happens
			// !!!!!!!!!!!!!!!                                         but do not copy if not necessary
			p.getFirst().forEach(assumption -> processAssumeStatement(assumption));

			IType type = rhs.getType();
			// note: there is no implicit typecasting in boogie. "real := int;" cannot happen. 
			if (TypeUtil.isBoolean(type)) {
				processBooleanAssign(targetVar, rhs);
			} else if (TypeUtil.isNumeric(type)) {
				processNumericAssign(targetVar, rhs);
			} else {
				// variables of unsupported types are assumed to be \top all the time
				mNewStates = mOldStates;
			}
			
			tmpNewStates.addAll(mNewStates);
		}

		mNewStates = tmpNewStates;
	}
	
	private void processBooleanAssign(String targetVar, Expression rhs) {
		Consumer<OctagonDomainState> action = s -> s.havocVar(targetVar);
		if (rhs instanceof BooleanLiteral) {
			BoolValue value = BoolValue.get(((BooleanLiteral) rhs).getValue());
			action = s -> s.assignBooleanVar(targetVar, value);
		} else if (rhs instanceof IdentifierExpression) {
			IdentifierExpression ie = (IdentifierExpression) rhs;
			if (BoogieAstUtil.isVariable(ie)) {
				String sourceVar = ie.getIdentifier();
				action = s -> s.copyVar(targetVar, sourceVar);
			}
		}
		
		// TODO calculate using BoolValue

		mOldStates.forEach(action);
		mNewStates = mOldStates;
	}
	
	private void processNumericAssign(String targetVar, Expression rhs) {
		Consumer<OctagonDomainState> action;
		action = s -> s.havocVar(targetVar); // default operation (if assignment cannot be interpreted)
		AffineExpression ae = mExprTransformer.affineExprCached(rhs);
		if (ae != null) {
			if (ae.isConstant()) {
				OctValue value = new OctValue(ae.getConstant());
				action = s -> s.assignNumericVarConstant(targetVar, value);
			} else {
				AffineExpression.OneVarForm ovf = ae.getOneVarForm();
				if (ovf != null) {
					action = s -> s.copyVar(targetVar, ovf.var);
					if (ovf.varSignum == -1) {
						action = action.andThen(s -> s.negateNumericVar(targetVar));
					}
					if (ovf.constant.signum() != 0) {
						action = action.andThen(s -> s.incrementNumericVar(targetVar, ovf.constant));
					}
				} else {
					// TODO project to intervals and calculate
				}
			}
		}
		mOldStates.forEach(action);
		mNewStates = mOldStates;
	}

	private void processHavocStatement(HavocStatement statement) {
		List<String> vars = new ArrayList<>();
		for (VariableLHS lhs : statement.getIdentifiers()) {
			vars.add(lhs.getIdentifier());
		}
		mOldStates.forEach(s -> s.havocVars(vars));
		mNewStates = mOldStates;
	}

	private void processAssumeStatement(Expression assumedFormula) {
		// TODO implement
		
		// note IfThenElseExpression can occur
		
		mNewStates = mOldStates; // note: returning old state is safe (but imprecise)
	}
}
