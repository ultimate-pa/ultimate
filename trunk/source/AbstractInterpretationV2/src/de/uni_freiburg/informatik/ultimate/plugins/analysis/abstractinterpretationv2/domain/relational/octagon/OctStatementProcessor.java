package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class OctStatementProcessor {

	private final OctPostOperator mPostOp;
	private final OctAssumeProcessor mAssumeProcessor;
	
	public OctStatementProcessor(OctPostOperator postOperator) {
		mPostOp = postOperator;
		mAssumeProcessor = new OctAssumeProcessor(postOperator);
	}

	public List<OctDomainState> processStatement(Statement statement, List<OctDomainState> oldStates) {
		if (statement instanceof AssignmentStatement) {
			return processAssignmentStatement((AssignmentStatement) statement, oldStates);
		} else if (statement instanceof AssumeStatement) {
			Expression assumption = ((AssumeStatement) statement).getFormula();
			return mAssumeProcessor.assume(assumption, oldStates);
		} else if (statement instanceof HavocStatement) {
			return processHavocStatement((HavocStatement) statement, oldStates);
		} else if (statement instanceof IfStatement) {
			// TODO support if it can occur
			String msg = "IfStatements are not supported by post-operator. Set block-encoding to single statements.";
			throw new UnsupportedOperationException(msg);
		} else if (statement instanceof Label) {
			return oldStates; // nothing to do
		} else {
			throw new UnsupportedOperationException("Unsupported type of statement: " + statement);
		}
	}

	private List<OctDomainState> processAssignmentStatement(AssignmentStatement statement,
			List<OctDomainState> oldStates) {

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
		List<Pair<String, Expression>> mapLhsToRhs = new ArrayList<>(length);
		List<Pair<String, String>> mapOrigVarToTmpVar = new ArrayList<>(length);
		for (int i = 0; i < length; ++i) {
			LeftHandSide l = lhs[i];

			if (l instanceof VariableLHS) {
				VariableLHS vLhs = (VariableLHS) l;
				String origVar = vLhs.getIdentifier();
				String tmpVar = "octTmp(" + origVar + ")"; // unique (origVar is unique + braces are not allowed)

				tmpVars.put(tmpVar, BoogieUtil.createTemporaryIBoogieVar(tmpVar, vLhs.getType()));
				mapLhsToRhs.add(new Pair<>(tmpVar, rhs[i]));
				mapOrigVarToTmpVar.add(new Pair<>(origVar, tmpVar));
			}
			// else: variables of unsupported types are assumed to be \top all the time
		}

		// add temporary variables
		List<OctDomainState> tmpStates = new ArrayList<>(oldStates.size());
		oldStates.forEach(oldState -> tmpStates.add(oldState.addVariables(tmpVars)));

		// (tmpVar := origExpr)*
		// note: oldStates may be modified (which is OK), since addVariables() returns only a shallow copy
		mapLhsToRhs.forEach(lhsToRhs -> processSingleAssignment(lhsToRhs.getFirst(), lhsToRhs.getSecond(), tmpStates));

		// (origVar := tmpVar)*
		tmpStates.forEach(tmpState -> tmpState.copyVars(mapOrigVarToTmpVar));

		// remove temporary variables
		List<OctDomainState> newStates = new ArrayList<>(oldStates.size());
		tmpStates.forEach(tmpState -> newStates.add(tmpState.removeVariables(tmpVars)));
		return newStates;
	}
	
	public List<OctDomainState> processSingleAssignment(String targetVar, Expression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates); // important! assign may un-bottomize some states!

		// note: there is no implicit typecasting in boogie. "real := int;" cannot happen. 
		IType type = rhs.getType();
		if (TypeUtil.isBoolean(type)) {
			return processBooleanAssign(targetVar, rhs, oldStates);
		} else if (TypeUtil.isNumeric(type)) {
			return processNumericAssign(targetVar, rhs, oldStates);
		} else {
			return oldStates; // variables of unsupported types are assumed to be \top all the time
		}
	}
	
	private List<OctDomainState> processBooleanAssign(String targetVar, Expression rhs,
			List<OctDomainState> oldStates) {

		Consumer<OctDomainState> action = s -> s.havocVar(targetVar); // default operation (if uninterpretable)

		if (rhs instanceof BooleanLiteral) {
			BoolValue value = BoolValue.get(((BooleanLiteral) rhs).getValue());
			action = s -> s.assignBooleanVar(targetVar, value);
		} else if (rhs instanceof IdentifierExpression) {
			IdentifierExpression ie = (IdentifierExpression) rhs;
			if (BoogieUtil.isVariable(ie)) {
				String sourceVar = ie.getIdentifier();
				action = s -> s.copyVar(targetVar, sourceVar);
			}
		} else {
			Expression notRhs = mPostOp.getExprTransformer().logicNegCached(rhs);
			return mPostOp.splitF(oldStates,
					stateList -> {
						stateList = mAssumeProcessor.assume(rhs, stateList);
						stateList = OctPostOperator.removeBottomStates(stateList); // important!
						stateList.forEach(state -> state.assignBooleanVar(targetVar, BoolValue.TRUE));
						return stateList;
					},
					stateList -> {
						stateList = mAssumeProcessor.assume(notRhs, stateList);
						stateList = OctPostOperator.removeBottomStates(stateList); // important!
						stateList.forEach(state -> state.assignBooleanVar(targetVar, BoolValue.FALSE));
						return stateList;
					});
		}

		oldStates.forEach(action);
		return oldStates;
	}
	
	private List<OctDomainState> processNumericAssign(String targetVar, Expression rhs,
			List<OctDomainState> oldStates) {

		List<Pair<List<Expression>, Expression>> paths = mPostOp.getExprTransformer().removeIfExprsCached(rhs);
		List<OctDomainState> result = new ArrayList<>();
		for (int i = 0; i < paths.size(); ++i) {
			Pair<List<Expression>, Expression> p = paths.get(i);
			List<OctDomainState> copiedOldStates = (i + 1 < paths.size()) ?
					mPostOp.deepCopy(oldStates) : oldStates; // as little copies as possible
			for (Expression assumption : p.getFirst()) {
				// This step is slow for deeply nested IfThenElseExpressions
				// same assumptions have to be assumed over and over again
				// TODO create BinaryTree instead of paths, which allows re-use of assumes
				copiedOldStates = mAssumeProcessor.assume(assumption, copiedOldStates);
			}
			copiedOldStates = OctPostOperator.removeBottomStates(copiedOldStates); // important!
			result.addAll(processNumericAssignWithoutIfs(targetVar, rhs, copiedOldStates));
		}
		return mPostOp.joinIfGeMaxParallelStates(result);
	}
	
	private List<OctDomainState> processNumericAssignWithoutIfs(String targetVar, Expression rhs,
			List<OctDomainState> oldStates) {
		
		AffineExpression ae = mPostOp.getExprTransformer().affineExprCached(rhs);
		if (ae != null) {
			AffineExpression.OneVarForm ovf;
			if (ae.isConstant()) {
				OctValue value = new OctValue(ae.getConstant());
				oldStates.forEach(s -> s.assignNumericVarConstant(targetVar, value));
				return oldStates;
			} else if ((ovf = ae.getOneVarForm()) != null) {
				Consumer<OctDomainState> action = s -> s.copyVar(targetVar, ovf.var);
				if (ovf.negVar) {
					action = action.andThen(s -> s.negateNumericVar(targetVar));
				} else {
					action = action.andThen(s -> s.incrementNumericVar(targetVar, ovf.constant));
				}
				oldStates.forEach(action);
				return oldStates;
			} else if (mPostOp.isFallbackAssignIntervalProjectionEnabled()) {
				return IntervalProjection.assignNumericVarAffine(targetVar, ae, oldStates);
			}
		} else if (mPostOp.isFallbackAssignIntervalProjectionEnabled()) { // no affine form found
			return IntervalProjection.assignNumericVarWithoutIfs(targetVar, rhs, oldStates);
		}

		// could not interpret rhs -- return safe over-approximation (targetVar := \top)
		oldStates.forEach(s -> s.havocVar(targetVar));
		return oldStates;
	}

	private List<OctDomainState> processHavocStatement(HavocStatement statement,
			List<OctDomainState> oldStates) {
		List<String> vars = new ArrayList<>();
		for (VariableLHS lhs : statement.getIdentifiers()) {
			vars.add(lhs.getIdentifier());
		}
		oldStates = OctPostOperator.removeBottomStates(oldStates); // important!
		oldStates.forEach(s -> s.havocVars(vars));
		return oldStates;
	}
	
}
