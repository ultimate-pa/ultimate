package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class BitvectorTranslation extends AExpressionTranslation {

	public BitvectorTranslation(TypeSizes m_TypeSizeConstants, FunctionDeclarations functionDeclarations) {
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
		default:
			return super.translateLiteral(main, node);
		}
	}
	
	@Override
	public RValue translateIntegerLiteral(ILocation loc, String val) {
		RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, m_TypeSizeConstants);
		return rVal;
	}
	
	@Override
	public Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, true, m_TypeSizeConstants, type, value);
	}


	@Override
	public Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		FunctionApplication func;

		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			if (type1.isUnsigned() != type2.isUnsigned()) {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			
			func = new FunctionApplication(loc, "=", new Expression[]{exp1, exp2});
			break;
		case IASTBinaryExpression.op_greaterEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvuge";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvuge", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvuge" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvsge";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsge", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsge" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_greaterThan:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvugt";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvugt", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvugt" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvsgt";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsgt", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsgt" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvule";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvule", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvule" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvsle";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsle", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvsle" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessThan:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvult";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvult", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvult" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				assert(m_FunctionDeclarations.checkParameters(type1, type2)):"bvslt";
				m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvslt", new CPrimitive(PRIMITIVE.BOOL), (CPrimitive) type1, (CPrimitive) type2);

				func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvslt" + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
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
		if(!m_FunctionDeclarations.checkParameters(typeLeft, typeRight)) {
			throw new IllegalArgumentException("incompatible types " + typeLeft + " " + typeRight);
		}
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			funcname = "bvsub";
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			funcname = "bvmul";
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			if (typeLeft.isUnsigned() && typeRight.isUnsigned()) {
				funcname = "bvudiv";
			} else if (!typeLeft.isUnsigned() && !typeRight.isUnsigned()) {
				funcname = "bvsdiv";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			if (typeLeft.isUnsigned() && typeRight.isUnsigned()) {
				funcname = "bvurem";
			} else if (!typeLeft.isUnsigned() && !typeRight.isUnsigned()) {
				funcname = "bvsrem";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			funcname = "bvadd";
			break;
		default:
			String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		
		m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, (CPrimitive) typeLeft, (CPrimitive) typeLeft, (CPrimitive) typeRight);
		func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + m_FunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), new Expression[]{left, right});

		return func;
	}

	@Override
	public Expression unaryMinusForInts(ILocation loc, Expression operand, CType type) {
		m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvneg", (CPrimitive) type, (CPrimitive) type);
		m_FunctionDeclarations.declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvadd", (CPrimitive) type, (CPrimitive) type, (CPrimitive) type);

		FunctionApplication negation = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvneg" + m_FunctionDeclarations.computeBitvectorSuffix(loc, (CPrimitive) type), new Expression[]{operand});
		
		return new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "bvadd" + m_FunctionDeclarations.computeBitvectorSuffix(loc, (CPrimitive) type, (CPrimitive) type), 
				new Expression[]{negation, constructLiteralForIntegerType(loc, (CPrimitive) type, BigInteger.ONE)});
	}

}
