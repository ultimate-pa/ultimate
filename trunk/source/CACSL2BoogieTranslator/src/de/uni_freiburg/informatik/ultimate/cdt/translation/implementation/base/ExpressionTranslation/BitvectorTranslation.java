package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizeConstants;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class BitvectorTranslation extends AbstractExpressionTranslation {

	public BitvectorTranslation(TypeSizeConstants m_TypeSizeConstants, FunctionDeclarations functionDeclarations) {
		super(m_TypeSizeConstants, functionDeclarations);
	}

	@Override
	public ResultExpression translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			CPrimitive cprimitive = new CPrimitive(PRIMITIVE.CHAR);
			int bitlength = 8 * m_TypeSizeConstants.getCPrimitiveToTypeSizeConstant().get(cprimitive);
			return new ResultExpression(new RValue(new BitvecLiteral(loc, val, bitlength), cprimitive));
		}
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, m_TypeSizeConstants);
			return new ResultExpression(rVal);
		}
		default:
			return super.translateLiteral(main, node);
		}
	}

	@Override
	public Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		FunctionApplication func;
		String identifier;

		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			if (type1.isUnsigned() != type2.isUnsigned()) {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, "=", new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_greaterEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				identifier = "bvuge";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				identifier = "bvsge";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, identifier, new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_greaterThan:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				identifier = "~bvugt";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				identifier = "~bvsgt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, identifier, new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_lessEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				identifier = "~bvule";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				identifier = "~bvsle";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, identifier, new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_lessThan:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				identifier = "~bvult";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				identifier = "~bvslt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, identifier, new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_notequals:
			if (type1.isUnsigned() != type2.isUnsigned()) {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, "!=", new Expression[]{exp1, exp2});
			break;
		default:
			throw new AssertionError("???");
		}
		
		return func;
	}

	@Override
	public Expression constructBinaryBitwiseShiftExpression(ILocation loc,
			int nodeOperator, Expression exp1, CPrimitive type1,
			Expression exp2, CPrimitive type2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expression createArithmeticExpression(int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight, ILocation loc) {
		FunctionApplication func;
		
		switch (op) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsub", new Expression[]{left, right});

			return func;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvmul", new Expression[]{left, right});

			return func;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			if (typeLeft.isUnsigned() && typeRight.isUnsigned()) {
				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvudiv", new Expression[]{left, right});
			} else if (!typeLeft.isUnsigned() && !typeRight.isUnsigned()) {
				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsdiv", new Expression[]{left, right});
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			
			return func;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
//			if (typeLeft.isUnsigned() && typeRight.isUnsigned()) {
//				func = new FunctionApplication(loc, "~bvudiv", new Expression[]{left, right});
//			} else if (!typeLeft.isUnsigned() && !typeRight.isUnsigned()) {
//				func = new FunctionApplication(loc, "~bvsdiv", new Expression[]{left, right});
//			} else {
//				throw new IllegalArgumentException("Mixed signed and unsigned");
//			}
//			
//			return func;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvadd", new Expression[]{left, right});

			return func;
		default:
			String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
}
