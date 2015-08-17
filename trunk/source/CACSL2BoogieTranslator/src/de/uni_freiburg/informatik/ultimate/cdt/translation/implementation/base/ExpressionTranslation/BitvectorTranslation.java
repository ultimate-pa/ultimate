package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class BitvectorTranslation extends AExpressionTranslation {

	public BitvectorTranslation(TypeSizes m_TypeSizeConstants, ITypeHandler typeHandler) {
		super(m_TypeSizeConstants, typeHandler);
	}

	@Override
	public ResultExpression translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			CPrimitive cprimitive = new CPrimitive(PRIMITIVE.CHAR);
			int bitlength = 8 * m_TypeSizes.getSize(PRIMITIVE.CHAR);
			return new ResultExpression(new RValue(new BitvecLiteral(loc, val, bitlength), cprimitive));
		}
		default:
			return super.translateLiteral(main, node);
		}
	}
	
	@Override
	public RValue translateIntegerLiteral(ILocation loc, String val) {
		RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, m_TypeSizes);
		return rVal;
	}
	
	@Override
	public Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, true, m_TypeSizes, type, value);
	}


	@Override
	public Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		if(!m_FunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final Expression result;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals:
			result = constructBinaryEqualsExpression(loc, nodeOperator, exp1, type1, exp2, type2);
			break;
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan:
			result = constructBinaryInequalityExpression(loc, nodeOperator, exp1, type1, exp2, type2);
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}
		
		return result;
	}
	
	
	public Expression constructBinaryInequalityExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		if(!m_FunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final String functionName;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_greaterEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				functionName = "bvuge";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				functionName = "bvsge";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_greaterThan:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				functionName = "bvugt";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				functionName = "bvsgt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessEqual:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				functionName = "bvule";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				functionName = "bvsle";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessThan:
			
			if (type1.isUnsigned() && type2.isUnsigned()) {
				functionName = "bvult";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				functionName = "bvslt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}
		declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, true, new CPrimitive(PRIMITIVE.BOOL), null, (CPrimitive) type1, (CPrimitive) type2);
		Expression result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName + m_FunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
		return result;
	}
	
	@Override
	public Expression constructBinaryBitwiseExpression(ILocation loc,
			int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight) {
		if(!m_FunctionDeclarations.checkParameters(typeLeft, typeRight)) {
			throw new IllegalArgumentException("incompatible types " + typeLeft + " " + typeRight);
		}
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
			funcname = "bvand";
			break;
		case IASTBinaryExpression.op_binaryOr:
			funcname = "bvor";
			break;
		case IASTBinaryExpression.op_binaryXor:
			funcname = "bvxor";
			break;
		case IASTBinaryExpression.op_shiftLeft:
			funcname = "bvshl";
			break;
		case IASTBinaryExpression.op_shiftRight:
			funcname = "bvashr";
			break;
		default:
			String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, typeLeft, null, typeLeft, typeRight);
		Expression func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + m_FunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), new Expression[]{left, right});
		return func;
	}
	
	@Override
	public Expression constructUnaryExpression(ILocation loc,
			int op, Expression expr, CPrimitive type) {
		final String funcname;
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			funcname = "bvnot";
			break;
		case IASTUnaryExpression.op_minus:
			funcname = "bvneg";
			break;
		default:
			String msg = "Unknown or unsupported unary expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, type, null, type);
		Expression func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + m_FunctionDeclarations.computeBitvectorSuffix(loc, type), new Expression[]{expr});
		return func;
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
		
		declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, typeLeft, null, typeLeft, typeRight);
		func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + m_FunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), new Expression[]{left, right});

		return func;
	}

	private void declareBitvectorFunction(ILocation loc, String prefixedFunctionName,
			boolean boogieResultTypeBool, CPrimitive resultCType, int[] indices, CPrimitive... paramCType) {
		String functionName = prefixedFunctionName.substring(1, prefixedFunctionName.length());
		Attribute[] attributes;
		if (indices == null) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName) });
		    attributes = new Attribute[] { attribute };
		} else {
		    Expression[] literalIndices = new IntegerLiteral[indices.length];
		    for (int i = 0; i < indices.length; ++i) {
		    	literalIndices[i] = new IntegerLiteral(loc, String.valueOf(indices[i]));
		    }
		    Attribute attribute1 = new NamedAttribute(loc, FunctionDeclarations.s_INDEX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName) });
		    Attribute attribute2 = new NamedAttribute(loc, FunctionDeclarations.s_INDEX_IDENTIFIER, literalIndices);
		    attributes = new Attribute[] { attribute1, attribute2 };
		}
		m_FunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, true, attributes, boogieResultTypeBool, resultCType, paramCType);
	}

//	@Override
	public void convert(ILocation loc, ResultExpression operand, CPrimitive resultType, TypeSizes typeSizeConstants) {
		int resultLength = m_TypeSizes.getSize(resultType.getType());
		int operandLength = m_TypeSizes.getSize(((CPrimitive) operand.lrVal.cType).getType());
		
		operand.lrVal.cType = resultType;
		
		if (resultLength == operandLength) {
		} else if (resultLength > operandLength) {
			int[] indices = new int[]{resultLength - operandLength};
			declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "sign_extend", false, resultType, indices, (CPrimitive) operand.lrVal.cType);
			FunctionApplication func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "sign_extendFrom" + m_FunctionDeclarations.computeBitvectorSuffix(loc, (CPrimitive) operand.lrVal.cType)
					                                                                                           + "To" + m_FunctionDeclarations.computeBitvectorSuffix(loc, resultType), new Expression[]{operand.lrVal.getValue()});
		    RValue rVal = new RValue(func, resultType);
			operand.lrVal = rVal;
		} else {
			
		}
	}




	

}
