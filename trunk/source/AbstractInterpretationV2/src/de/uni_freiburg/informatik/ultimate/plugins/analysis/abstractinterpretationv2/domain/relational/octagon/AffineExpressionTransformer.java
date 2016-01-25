package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.TypeCheckException;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.LinearConstraint;

public class AffineExpressionTransformer {
	
	public static AffineExpression transformNumeric(Expression e) {
		assert TypeUtil.isNumeric(e.getType()) : "Tried numeric transformation for " + e;
		if (e instanceof IntegerLiteral) {
			String value = ((IntegerLiteral) e).getValue();
			return new AffineExpression(new BigDecimal(value));
		} else if (e instanceof RealLiteral) {
			String value = ((RealLiteral) e).getValue();
			return new AffineExpression(new BigDecimal(value));
		} else if (e instanceof IdentifierExpression) {
			String varName = ((IdentifierExpression) e).getIdentifier();
			Map<String, BigDecimal> coefficients = Collections.singletonMap(varName, BigDecimal.ONE);
			return new AffineExpression(coefficients, BigDecimal.ZERO);
		} else if (e instanceof UnaryExpression) {
			return transformNumericUnaryExpression((UnaryExpression) e);
		} else if (e instanceof BinaryExpression) {
			return transformNumericBinaryExpression((BinaryExpression) e);
		}
		return null;
	}

	private static AffineExpression transformNumericUnaryExpression(UnaryExpression e) {
		switch (e.getOperator()) {
		case ARITHNEGATIVE:
			AffineExpression sub = transformNumeric(e.getExpr());
			return sub == null ? null : sub.negate();
		default:
			return null;
		}
	}
	
	private static AffineExpression transformNumericBinaryExpression(BinaryExpression e) {
		AffineExpression left = transformNumeric(e.getLeft());
		if (left == null) { return null; }
		AffineExpression right = transformNumeric(e.getRight());
		if (right == null) { return null; }
		boolean isInteger = TypeUtil.isNumericInt(e.getType());
		switch (e.getOperator()) {
		case ARITHDIV:
			return left.divide(right, isInteger);
		case ARITHMINUS:
			return left.add(right.negate());
		case ARITHMOD:
			return left.modulo(right);
		case ARITHMUL:
			return left.multiply(right);
		case ARITHPLUS:
			return left.add(right);
		default:
			return null;
		}
	}
	
	
}
