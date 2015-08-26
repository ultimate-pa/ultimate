package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public abstract class AExpressionTranslation {
	
	protected final FunctionDeclarations m_FunctionDeclarations;
	protected final TypeSizes m_TypeSizes;

	public AExpressionTranslation(TypeSizes typeSizeConstants, ITypeHandler typeHandler) {
		super();
		this.m_TypeSizes = typeSizeConstants;
		this.m_FunctionDeclarations = new FunctionDeclarations(typeHandler, m_TypeSizes);
	}

	public ResultExpression translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant:
		{
			String val = new String(node.getValue());
			val = ISOIEC9899TC3.handleFloatConstant(val, loc, main);
			return new ResultExpression(new RValue(new RealLiteral(loc, val), new CPrimitive(PRIMITIVE.FLOAT)));
		}
		case IASTLiteralExpression.lk_char_constant:
			throw new AssertionError("To be handled by subclass");
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = translateIntegerLiteral(loc, val);
			return new ResultExpression(rVal);
		}
		case IASTLiteralExpression.lk_string_literal:
			// Translate string to uninitialized char pointer
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, MemoryHandler.POINTER_TYPE) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(PRIMITIVE.CHAR)));
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ResultExpression(new ArrayList<Statement>(), rvalue, decls, auxVars);
		case IASTLiteralExpression.lk_false:
			return new ResultExpression(new RValue(new BooleanLiteral(loc, false), new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_true:
			return new ResultExpression(new RValue(new BooleanLiteral(loc, true), new CPrimitive(PRIMITIVE.INT)));
		default:
			String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
	
	
	public abstract Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructBinaryBitwiseExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructUnaryExpression(ILocation loc, int nodeOperator, Expression exp, CPrimitive type);
	public abstract Expression createArithmeticExpression(int op, Expression left, CPrimitive typeLeft, Expression right, CPrimitive typeRight, ILocation loc);
	
	
	public Expression constructBinaryEqualityExpression(ILocation loc, int nodeOperator, Expression exp1, CType type1, Expression exp2, CType type2) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return new BinaryExpression(loc, BinaryExpression.Operator.COMPEQ, exp1, exp2);
		} else 	if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return new BinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, exp1, exp2);
		} else {
			throw new IllegalArgumentException("operator is neither equals nor not equals");
		}
	}
	
	public abstract RValue translateIntegerLiteral(ILocation loc, String val);
	
	public abstract Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value);
	public Expression constructLiteralForFloatingType(ILocation loc, CPrimitive inputPrimitive, BigInteger zero) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	public FunctionDeclarations getFunctionDeclarations() {
		return m_FunctionDeclarations;
	}
	
	public CPrimitive determineResultOfUsualArithmeticConversions_Integer(CPrimitive typeLeft, CPrimitive typeRight) {
		
		if (typeLeft.equals(typeRight)) {
			return typeLeft;
		} else if ((typeLeft.isUnsigned() && typeRight.isUnsigned()) || (!typeLeft.isUnsigned() && !typeRight.isUnsigned())) {
			Integer sizeLeft = m_TypeSizes.getSize(typeLeft.getType());
			Integer sizeRight = m_TypeSizes.getSize(typeRight.getType());
			
			if (sizeLeft.compareTo(sizeRight) >= 0) {
				return typeLeft;
			} else {
				return typeRight;
			}			
		} else {
			CPrimitive unsignedType;
			CPrimitive signedType;
			
			if (typeLeft.isUnsigned()) {
				unsignedType = typeLeft;
				signedType = typeRight;
			} else {
				unsignedType = typeRight;
				signedType = typeLeft;
			}
			
			if (m_TypeSizes.getSize(unsignedType.getType()).compareTo(m_TypeSizes.getSize(signedType.getType())) >= 0) {
				return unsignedType;
			} else {
				return signedType;
			}
		}
	}
	
	/**
	 * Apply usual arithmetic conversion according to 6.3.1.8 of the C11 
	 * standard.
	 * Therefore we determine the determine the CType of the result.
	 * Afterwards we convert both operands to the result CType.
	 * 
	 * TODO: This is not correct for complex types. E.g., if double and
	 * complex float are operands, the complex float is converted to a
	 * complex double not to a (real double).
	 * Fixing this will be postponed until we want to support complex types.
	 */
	public void usualArithmeticConversions(Dispatcher main, ILocation loc, 
			ResultExpression leftRex, ResultExpression rightRex) {
		final CPrimitive leftPrimitive = getCorrespondingPrimitiveType(leftRex.lrVal.cType);
		final CPrimitive rightPrimitive = getCorrespondingPrimitiveType(rightRex.lrVal.cType);
		if (leftPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, leftRex);
		}
		if (rightPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, rightRex);
		}

		final CPrimitive resultType = determineResultOfUsualArithmeticConversions(
				(CPrimitive) leftRex.lrVal.cType, 
				(CPrimitive) rightRex.lrVal.cType);

		convertIfNecessary(loc, leftRex, resultType);
		convertIfNecessary(loc, rightRex, resultType);
		
		if (!leftRex.lrVal.cType.equals(resultType)) {
			throw new AssertionError("conversion failed"); 
		}
		if (!rightRex.lrVal.cType.equals(resultType)) {
			throw new AssertionError("conversion failed"); 
		}
	}


	/**
	 * Convert ResultExpression to resultType if its type is not already
	 * resultType.
	 */
	private void convertIfNecessary(ILocation loc, ResultExpression operand,
			CPrimitive resultType) {
		if (operand.lrVal.cType.equals(resultType)) {
			// do nothing
		} else {
			convert(loc, operand, resultType);
		}
	}

	private CPrimitive determineResultOfUsualArithmeticConversions(
			CPrimitive leftPrimitive, CPrimitive rightPrimitive) {
		if (leftPrimitive.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE
				|| rightPrimitive.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
			if (leftPrimitive.getType() == PRIMITIVE.COMPLEX_LONGDOUBLE 
					|| rightPrimitive.getType() == PRIMITIVE.COMPLEX_LONGDOUBLE) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == PRIMITIVE.COMPLEX_DOUBLE 
					|| rightPrimitive.getType() == PRIMITIVE.COMPLEX_DOUBLE) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == PRIMITIVE.COMPLEX_FLOAT 
					|| rightPrimitive.getType() == PRIMITIVE.COMPLEX_FLOAT) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == PRIMITIVE.LONGDOUBLE 
					|| rightPrimitive.getType() == PRIMITIVE.LONGDOUBLE) {
				return new CPrimitive(PRIMITIVE.LONGDOUBLE);
			} else if (leftPrimitive.getType() == PRIMITIVE.DOUBLE 
					|| rightPrimitive.getType() == PRIMITIVE.DOUBLE) {
				return new CPrimitive(PRIMITIVE.DOUBLE);
			} else if (leftPrimitive.getType() == PRIMITIVE.FLOAT 
					|| rightPrimitive.getType() == PRIMITIVE.FLOAT) {
				return new CPrimitive(PRIMITIVE.FLOAT);
			} else {
				throw new AssertionError("unknown FLOATTYPE " + leftPrimitive +", " + rightPrimitive);
			}
		} else if (leftPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE
				&& rightPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
			return determineResultOfUsualArithmeticConversions_Integer(leftPrimitive, rightPrimitive);
		} else {
			throw new AssertionError("unsupported combination of CPrimitives: " 
					+ leftPrimitive + " and " + rightPrimitive);
		} 
	}

	/**
	 * If CType is CEnum return int (since C standard 6.4.4.3.2 says 
	 * "An identifier declared as an enumeration constant has type int.")
	 * If CType is CPrimitive return it.
	 * Otherwise throw an Exception that conversion will be impossible.  
	 */
	private CPrimitive getCorrespondingPrimitiveType(CType cType) {
		if (cType instanceof CPrimitive) {
			return (CPrimitive) cType; 
		} else if (cType instanceof CEnum) {
			return new CPrimitive(PRIMITIVE.INT);
		} else {
			throw new UnsupportedOperationException("unable to apply usual arithmetic conversions to " + cType);
		}
	}

	public abstract void convert(ILocation loc, ResultExpression operand, CType resultType);
	
	/**
	 * Perform the integer promotions a specified in C11 6.3.1.1.2 on the
	 * operand.
	 */
	public abstract void doIntegerPromotion(ILocation loc, ResultExpression operand);
	
	public boolean integerPromotionNeeded(CPrimitive cPrimitive) {
		if (cPrimitive.equals(CPrimitive.PRIMITIVE.CHAR) || cPrimitive.equals(CPrimitive.PRIMITIVE.CHAR16) ||
			cPrimitive.equals(CPrimitive.PRIMITIVE.CHAR32) || cPrimitive.equals(CPrimitive.PRIMITIVE.SCHAR) ||
			cPrimitive.equals(CPrimitive.PRIMITIVE.SHORT) || cPrimitive.equals(CPrimitive.PRIMITIVE.UCHAR) ||
			cPrimitive.equals(CPrimitive.PRIMITIVE.USHORT) || cPrimitive.equals(CPrimitive.PRIMITIVE.WCHAR)) {
			return true;
		} else {
			return false;
		}
	}
	
	public CPrimitive determineResultOfIntegerPromotion(CPrimitive cPrimitive) {
		int argBitLength = m_TypeSizes.getSize(cPrimitive.getType()) * 8;
		int intLength = m_TypeSizes.getSize(CPrimitive.PRIMITIVE.INT) * 8;
		
		if (argBitLength < intLength || !cPrimitive.isUnsigned()) {
			return new CPrimitive(PRIMITIVE.INT);
		} else {
			return new CPrimitive(PRIMITIVE.UINT);
		}
	}
	

	/**
	 * In our Lindenmann-Hoenicke memory model, we use an array for all
	 * integer data on the heap. This method returns the CType that we use to
	 * represents this data.
	 */
	public CPrimitive getCTypeOfIntArray() {
		return new CPrimitive(PRIMITIVE.INT);
	}

	/**
	 * In our Lindenmann-Hoenicke memory model, we use an array for all
	 * floating type data on the heap. This method returns the CType that we 
	 * use to represent this data.
	 */
	public CPrimitive getCTypeOfFloatingArray() {
		return new CPrimitive(PRIMITIVE.FLOAT);
	}
	
	/**
	 * In our Lindenmann-Hoenicke memory model, a pointer is a struct of two
	 * integer data types. This method returns the CType of the structs
	 * components.
	 */
	public CPrimitive getCTypeOfPointerComponents() {
		return new CPrimitive(PRIMITIVE.INT);
	}


	
}
