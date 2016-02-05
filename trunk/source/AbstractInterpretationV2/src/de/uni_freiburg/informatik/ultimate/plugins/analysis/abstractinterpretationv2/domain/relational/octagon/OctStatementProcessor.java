package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

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
	private final ExpressionTransformer mExprTransformer;
	private final OctAssumeProcessor mAssumeProcessor;
	
	public OctStatementProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mExprTransformer = new ExpressionTransformer();
		mAssumeProcessor = new OctAssumeProcessor(logger, symbolTable, mExprTransformer);
	}

	public List<OctagonDomainState> processStatement(Statement statement, List<OctagonDomainState> oldStates) {
		if (statement instanceof AssignmentStatement) {
			return processAssignmentStatement((AssignmentStatement) statement, oldStates);
		} else if (statement instanceof AssumeStatement) {
			Expression assumption = ((AssumeStatement) statement).getFormula();
			return mAssumeProcessor.assume(assumption, oldStates);
		} else if (statement instanceof HavocStatement) {
			return processHavocStatement((HavocStatement) statement, oldStates);
		} else if (statement instanceof IfStatement) {
			// TODO support if it can occur
			String msg = "IfStatements are not supported by post-operator. Switch block-encoding to single statements.";
			throw new UnsupportedOperationException(msg);
		} else if (statement instanceof Label) {
			return oldStates; // nothing to do
		} else {
			throw new UnsupportedOperationException("Unsupported type of statement: " + statement);
		}
	}

	private List<OctagonDomainState> processAssignmentStatement(AssignmentStatement statement,
			List<OctagonDomainState> oldStates) {

		LeftHandSide[] lhs = statement.getLhs();
		Expression[] rhs = statement.getRhs();
		assert lhs.length == rhs.length : "Unbalanced assignment: " + statement;
		int length = lhs.length;		
		if (length == 1) {
			LeftHandSide l = lhs[0];
			if (l instanceof VariableLHS) {
				return processSingleAssignment(((VariableLHS) l).getIdentifier(), rhs[0], oldStates);
			} else {
				// variables of unsupported types (e.g. arrays) are assumed to be \top all the time
				return oldStates;
			}
		}
		Map<String, IBoogieVar> tmpVars = new HashMap<>();
		Map<String, String> mapTmpVarToOrigVar = new HashMap<>();
		Map<String, Expression> mapLhsToRhs = new HashMap<>();
		for (int i = 0; i < length; ++i) {
			LeftHandSide l = lhs[i];
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
		List<OctagonDomainState> tmpStates = new ArrayList<>(oldStates.size());
		oldStates.forEach(oldState -> tmpStates.add(oldState.addVariables(tmpVars)));

		// (tmpVar := origExpr)*
		mapLhsToRhs.entrySet().forEach(
				lhsToRhs -> processSingleAssignment(lhsToRhs.getKey(), lhsToRhs.getValue(), tmpStates));

		// (origVar := tmpVar)*
		tmpStates.forEach(tmpState -> tmpState.copyVars(mapTmpVarToOrigVar));

		// remove temporary variables
		List<OctagonDomainState> newStates = new ArrayList<>(oldStates.size());
		tmpStates.forEach(tmpState -> newStates.add(tmpState.removeVariables(tmpVars)));
		return newStates;
	}
	
	public List<OctagonDomainState> processSingleAssignment(String targetVar, Expression rhs,
			List<OctagonDomainState> oldStates) {

		List<Pair<List<Expression>, Expression>> paths = mExprTransformer.removeIfExprsCached(rhs);
		List<OctagonDomainState> result = new ArrayList<>();
		
		for (int i = 0; i < paths.size(); ++i) {
			Pair<List<Expression>, Expression> p = paths.get(i);

			List<OctagonDomainState> copiedOldStates;
			if (i + 1 < paths.size()) {
				copiedOldStates = deepCopy(oldStates);
			} else {
				copiedOldStates = oldStates; // skip one copy -- original oldState is not needed any more
				// For assignments without IfThenElseExpressions => no copy at all
			}

			for (Expression assumption : p.getFirst()) {
				// This step is slow for deeply nested IfThenElseExpressions
				// same assumptions have to be assumed over and over again
				// TODO create BinaryTree instead of paths, which allows re-use of assumes
				copiedOldStates = mAssumeProcessor.assume(assumption, copiedOldStates);
			}

			// note: there is no implicit typecasting in boogie. "real := int;" cannot happen. 
			IType type = rhs.getType();
			List<OctagonDomainState> newStates = new ArrayList<>();
			if (TypeUtil.isBoolean(type)) {
				newStates = processBooleanAssign(targetVar, rhs, copiedOldStates);
			} else if (TypeUtil.isNumeric(type)) {
				newStates = processNumericAssign(targetVar, rhs, copiedOldStates);
			} else {
				// variables of unsupported types are assumed to be \top all the time
				newStates = oldStates;
			}

			// TODO merge when maxParallelStates reached
			result.addAll(newStates);
		}
		return result;
	}
	
	private List<OctagonDomainState> processBooleanAssign(String targetVar, Expression rhs,
			List<OctagonDomainState> oldStates) {

		Consumer<OctagonDomainState> action = s -> s.havocVar(targetVar); // default operation (if uninterpretable)

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

		oldStates.forEach(action);
		return oldStates;
	}
	
	private List<OctagonDomainState> processNumericAssign(String targetVar, Expression rhs,
			List<OctagonDomainState> oldStates) {
		
		Consumer<OctagonDomainState> action = s -> s.havocVar(targetVar); // default operation (if uninterpretable)

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
		oldStates.forEach(action);
		return oldStates;
	}

	private List<OctagonDomainState> processHavocStatement(HavocStatement statement,
			List<OctagonDomainState> oldStates) {
		List<String> vars = new ArrayList<>();
		for (VariableLHS lhs : statement.getIdentifiers()) {
			vars.add(lhs.getIdentifier());
		}
		oldStates.forEach(s -> s.havocVars(vars));
		return oldStates;
	}
	
	private static List<OctagonDomainState> deepCopy(List<OctagonDomainState> states) {
		List<OctagonDomainState> copy = new ArrayList<>(states.size());
		states.forEach(state -> copy.add(state.deepCopy()));
		return copy; 
	}

}
