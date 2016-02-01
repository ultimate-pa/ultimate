package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieAstUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class OctAssumeProcessor {

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	private ExpressionTransformer mExprTransformer;

	private List<OctagonDomainState> mOldStates;
	private List<OctagonDomainState> mNewStates;

	public OctAssumeProcessor(Logger logger, BoogieSymbolTable symbolTable, ExpressionTransformer exprTransformer) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mExprTransformer = exprTransformer;
	}
	
	public List<OctagonDomainState> assume(List<OctagonDomainState> oldStates, Expression assumption) {
		List<Pair<List<Expression>, Expression>> paths = mExprTransformer.removeIfExprsCached(assumption);
		if (paths.size() > 1) { // there was an IfThenElseExpression
			// TODO recursively remove IfThenElseExpression from conditions
			// TODO assume selected part ("then" or "else")
			return oldStates; // safe over-approximation
		} else {
			assert paths.get(0).getFirst().isEmpty() && paths.get(0).getSecond() == assumption;
			// TODO processBooleanOperations(assumption, false);
			return oldStates; // safe over-approximation
		}
	}
	
	private void processBooleanOperations(Expression e, boolean isNegated) {
		if (e instanceof BinaryExpression) {
			BinaryExpression be = (BinaryExpression) e;
			Expression left = be.getLeft();
			Expression right = be.getRight();
			if (TypeUtil.isNumeric(left.getType()) && TypeUtil.isNumeric(right.getType())) {
				AffineExpression leftAffine = mExprTransformer.affineExprCached(left);
				AffineExpression rightAffine = mExprTransformer.affineExprCached(right);
				AffineExpression ae = leftAffine.subtract(rightAffine);
				
				Operator op = be.getOperator();
				if (isNegated) {
					op = negateRelOp(op);
				}
				// TODO
				switch (op) {
				case COMPEQ:
					// TODO split
				case COMPNEQ:
				case COMPLEQ:
				case COMPGT:
				case COMPLT:
				case COMPGEQ:
				default:
					throw new IllegalArgumentException("Not an relational operator: " + op);
				}
			}
			
		}
	}

	private Operator negateRelOp(Operator relOp) {
		switch (relOp) {
		case COMPEQ:
			return Operator.COMPNEQ;
		case COMPNEQ:
			return Operator.COMPEQ;
		case COMPLEQ:
			return Operator.COMPGT;
		case COMPGT:
			return Operator.COMPLEQ;
		case COMPLT:
			return Operator.COMPGEQ;
		case COMPGEQ:
			return Operator.COMPLT;
		default:
			throw new IllegalArgumentException("Not an relational operator: " + relOp);
		}
	}
	
//	private void processBinaryExpr() {
//		
//	}

}
