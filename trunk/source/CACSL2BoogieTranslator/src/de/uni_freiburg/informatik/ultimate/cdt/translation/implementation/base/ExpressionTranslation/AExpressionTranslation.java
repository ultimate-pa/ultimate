/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
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

	public ExpressionResult translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant:
		{
			String val = new String(node.getValue());
			val = ISOIEC9899TC3.handleFloatConstant(val, loc, main);
			return new ExpressionResult(new RValue(new RealLiteral(loc, val), new CPrimitive(PRIMITIVE.FLOAT)));
		}
		case IASTLiteralExpression.lk_char_constant:
			throw new AssertionError("To be handled by subclass");
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = translateIntegerLiteral(loc, val);
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_string_literal:
			// Translate string to uninitialized char pointer
			CPointer pointerType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET, pointerType);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, main.typeHandler.constructPointerType(loc)) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), pointerType);
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, auxVars);
		case IASTLiteralExpression.lk_false:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, false), new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_true:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, true), new CPrimitive(PRIMITIVE.INT)));
		default:
			String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
	
	
	public abstract Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructBinaryBitwiseExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructUnaryExpression(ILocation loc, int nodeOperator, Expression exp, CPrimitive type);
	public abstract Expression constructArithmeticExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	
	
	public Expression constructBinaryEqualityExpression(ILocation loc, int nodeOperator, Expression exp1, CType type1, Expression exp2, CType type2) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, exp1, exp2);
		} else 	if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, exp1, exp2);
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
			ExpressionResult leftRex, ExpressionResult rightRex) {
		final CPrimitive leftPrimitive = getCorrespondingPrimitiveType(leftRex.lrVal.getCType());
		final CPrimitive rightPrimitive = getCorrespondingPrimitiveType(rightRex.lrVal.getCType());
		if (leftPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, leftRex);
		}
		if (rightPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, rightRex);
		}

		final CPrimitive resultType = determineResultOfUsualArithmeticConversions(
				(CPrimitive) leftRex.lrVal.getCType(), 
				(CPrimitive) rightRex.lrVal.getCType());

		convertIfNecessary(loc, leftRex, resultType);
		convertIfNecessary(loc, rightRex, resultType);
		
		if (!leftRex.lrVal.getCType().equals(resultType)) {
			throw new AssertionError("conversion failed"); 
		}
		if (!rightRex.lrVal.getCType().equals(resultType)) {
			throw new AssertionError("conversion failed"); 
		}
	}


	/**
	 * Convert ResultExpression to resultType if its type is not already
	 * resultType.
	 */
	private void convertIfNecessary(ILocation loc, ExpressionResult operand,
			CPrimitive resultType) {
		if (operand.lrVal.getCType().equals(resultType)) {
			// do nothing
		} else {
			convertIntToInt(loc, operand, resultType);
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

	public abstract void convertIntToInt(ILocation loc, ExpressionResult operand, CPrimitive resultType);
	
	/**
	 * Perform the integer promotions a specified in C11 6.3.1.1.2 on the
	 * operand.
	 */
	public abstract void doIntegerPromotion(ILocation loc, ExpressionResult operand);
	
	public boolean integerPromotionNeeded(CPrimitive cPrimitive) {
		if (cPrimitive.getType().equals(CPrimitive.PRIMITIVE.CHAR) || 
//			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.CHAR16) ||
//			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.CHAR32) || 
			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.SCHAR) ||
			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.SHORT) || 
			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.UCHAR) ||
//			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.WCHAR) || 
			cPrimitive.getType().equals(CPrimitive.PRIMITIVE.USHORT)) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Try to get the value of RValue rval. Returns null if extraction
	 * is impossible. Extraction might succeed if rval represents a constant
	 * value. Extraction fails, e.g., if rval represents a variable.
	 * @param expr
	 * @return
	 */
	public BigInteger extractIntegerValue(RValue rval) {
		return extractIntegerValue(rval.getValue(), rval.getCType());
	}
	
	public abstract BigInteger extractIntegerValue(Expression expr, CType cType);
	
		
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
	public abstract CPrimitive getCTypeOfPointerComponents();

	public void convertPointerToInt(Dispatcher main, ILocation loc, ExpressionResult rexp,
			CPrimitive newType) {
		String prefixedFunctionName = declareConvertPointerToIntFunction(main,
				loc, newType);
		Expression pointerExpression = rexp.lrVal.getValue();
		Expression intExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {pointerExpression});
		RValue rValue = new RValue(intExpression, newType, false, false);
		rexp.lrVal = rValue;
	}

	private String declareConvertPointerToIntFunction(Dispatcher main, ILocation loc, CPrimitive newType) {
		String functionName = "convertPointerTo" + newType.toString();
		String prefixedFunctionName = "~" + functionName;
		if (!m_FunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType resultASTType = main.typeHandler.ctype2asttype(loc, newType);
			ASTType paramASTType = main.typeHandler.constructPointerType(loc);
			m_FunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}
	
	public void convertIntToPointer(Dispatcher main, ILocation loc, ExpressionResult rexp,
			CPointer newType) {
		boolean overapproximate = false;
		if (overapproximate) {
			String prefixedFunctionName = declareConvertIntToPointerFunction(main, loc, (CPrimitive) rexp.lrVal.getCType());
			Expression intExpression = rexp.lrVal.getValue();
			Expression pointerExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {intExpression});
			RValue rValue = new RValue(pointerExpression, newType, false, false);
			rexp.lrVal = rValue;
		} else {
			convertIntToInt(loc, rexp, getCTypeOfPointerComponents());
			Expression zero = constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), BigInteger.ZERO);
			RValue rValue = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(zero, rexp.lrVal.getValue(), loc), newType, false, false);
			rexp.lrVal = rValue;
		}
	}
	
	private String declareConvertIntToPointerFunction(Dispatcher main, ILocation loc, CPrimitive newType) {
		String functionName = "convert" + newType.toString() + "toPointer";
		String prefixedFunctionName = "~" + functionName;
		if (!m_FunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType resultASTType = main.typeHandler.constructPointerType(loc); 
			ASTType paramASTType = main.typeHandler.ctype2asttype(loc, newType);
			m_FunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}

	public void convertFloatToInt(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		throw new UnsupportedSyntaxException(loc, "conversion from float to int not yet implemented");
	}

	public void convertIntToFloat(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		throw new UnsupportedSyntaxException(loc, "conversion from int to float not yet implemented");
	}
	
	public void convertFloatToFloat(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		throw new UnsupportedSyntaxException(loc, "conversion from float to float not yet implemented");
	}
	
	
	public abstract void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType ctype, List<Statement> stmt);
	
}
