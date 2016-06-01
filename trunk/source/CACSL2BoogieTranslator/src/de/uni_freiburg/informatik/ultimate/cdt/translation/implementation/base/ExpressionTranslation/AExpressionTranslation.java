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

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION;

public abstract class AExpressionTranslation {
	
	protected final FunctionDeclarations mFunctionDeclarations;
	protected final TypeSizes mTypeSizes;
	protected final ITypeHandler mTypeHandler;
	protected final IPointerIntegerConversion mPointerIntegerConversion;


	public AExpressionTranslation(TypeSizes typeSizes, ITypeHandler typeHandler, 
			POINTER_INTEGER_CONVERSION pointerIntegerConversion) {
		super();
		mTypeSizes = typeSizes;
		mFunctionDeclarations = new FunctionDeclarations(typeHandler, mTypeSizes);
		mTypeHandler = typeHandler;
		switch (pointerIntegerConversion) {
		case IdentityAxiom:
			throw new UnsupportedOperationException("not yet implemented " + POINTER_INTEGER_CONVERSION.IdentityAxiom);
		case NonBijectiveMapping:
			mPointerIntegerConversion = new NonBijectiveMapping(this, mTypeHandler);
			break;
		case NutzBijection:
			throw new UnsupportedOperationException("not yet implemented " + POINTER_INTEGER_CONVERSION.NutzBijection);
		case Overapproximate:
			mPointerIntegerConversion = new OverapproximationUF(this, mFunctionDeclarations, mTypeHandler);
			break;
		default:
			throw new UnsupportedOperationException("unknown value " + pointerIntegerConversion);
		
		}
	}

	public ExpressionResult translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant:
		{
			final String val = new String(node.getValue());
			final RValue rVal = translateFloatingLiteral(loc, val);
			assert rVal != null : "result must not be null";
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_char_constant:
			throw new AssertionError("To be handled by subclass");
		case IASTLiteralExpression.lk_integer_constant:
		{
			final String val = new String(node.getValue());
			final RValue rVal = translateIntegerLiteral(loc, val);
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_string_literal:
			// Translate string to uninitialized char pointer
			final CPointer pointerType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
			final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, pointerType);
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, mTypeHandler.constructPointerType(loc)) });
			final RValue rvalue = new RValue(new IdentifierExpression(loc, tId), pointerType);
			final ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, auxVars);
		case IASTLiteralExpression.lk_false:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, false), new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_true:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, true), new CPrimitive(PRIMITIVE.INT)));
		default:
			final String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
	
	
	public final Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		//TODO: Check that types coincide
		if (type1.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE || type2.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
			return constructBinaryComparisonFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		} else {
			return constructBinaryComparisonIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
	}
	public final Expression constructBinaryBitwiseExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		//TODO: Check that types coincide
		if (type1.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE || type2.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
		} else {
			return constructBinaryBitwiseIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
	}
	public final Expression constructUnaryExpression(ILocation loc, int nodeOperator, Expression exp, CPrimitive type) {
		if (type.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
			return constructUnaryFloatingPointExpression(loc, nodeOperator, exp, type);
		} else {
			return constructUnaryIntegerExpression(loc, nodeOperator, exp, type);
		}
	}
	public final Expression constructArithmeticExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		//TODO: Check that types coincide
		if (type1.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE || type2.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
			return constructArithmeticFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		} else {
			return constructArithmeticIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
	}
	
	public abstract Expression constructBinaryComparisonIntegerExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructBinaryBitwiseIntegerExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructUnaryIntegerExpression(ILocation loc, int nodeOperator, Expression exp, CPrimitive type);
	public abstract Expression constructArithmeticIntegerExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructBinaryComparisonFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);
	public abstract Expression constructUnaryFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp, CPrimitive type);
	public abstract Expression constructArithmeticFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	
	public final Expression constructBinaryEqualityExpression(ILocation loc, int nodeOperator, Expression exp1, CType type1, Expression exp2, CType type2) {
		if (type1.isRealFloatingType() || type2.isRealFloatingType()) {
			return constructBinaryEqualityExpression_Floating(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructBinaryEqualityExpression_Integer(loc, nodeOperator, exp1, type1, exp2, type2);
	}
	
	public abstract Expression constructBinaryEqualityExpression_Floating(ILocation loc, int nodeOperator, Expression exp1, CType type1, Expression exp2, CType type2);	
	public abstract Expression constructBinaryEqualityExpression_Integer(ILocation loc, int nodeOperator, Expression exp1, CType type1, Expression exp2, CType type2);
	
	public abstract RValue translateIntegerLiteral(ILocation loc, String val);
	
	public abstract RValue translateFloatingLiteral(ILocation loc, String val);
	
	public abstract Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value);
	public Expression constructLiteralForFloatingType(ILocation loc, CPrimitive inputPrimitive, BigInteger zero) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	public FunctionDeclarations getFunctionDeclarations() {
		return mFunctionDeclarations;
	}
	
	public CPrimitive determineResultOfUsualArithmeticConversions_Integer(CPrimitive typeLeft, CPrimitive typeRight) {
		
		if (typeLeft.equals(typeRight)) {
			return typeLeft;
		} else if ((typeLeft.isUnsigned() && typeRight.isUnsigned()) || (!typeLeft.isUnsigned() && !typeRight.isUnsigned())) {
			final Integer sizeLeft = mTypeSizes.getSize(typeLeft.getType());
			final Integer sizeRight = mTypeSizes.getSize(typeRight.getType());
			
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
			
			if (mTypeSizes.getSize(unsignedType.getType()).compareTo(mTypeSizes.getSize(signedType.getType())) >= 0) {
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
	public void usualArithmeticConversions(ILocation loc, 
			ExpressionResult leftRex, ExpressionResult rightRex) {
		final CPrimitive leftPrimitive = (CPrimitive) 
				CEnum.replaceEnumWithInt(leftRex.lrVal.getCType()); 
		final CPrimitive rightPrimitive = (CPrimitive) 
				CEnum.replaceEnumWithInt(leftRex.lrVal.getCType()); 
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
			if (operand.lrVal.getCType().isIntegerType()) {
				if (resultType.isIntegerType()) {
					convertIntToInt(loc, operand, resultType);
				} else if (resultType.isRealFloatingType()) {
					convertIntToFloat(loc, operand, resultType);
				} else {
					throw new UnsupportedSyntaxException(loc, "conversion from " + operand.lrVal.getCType() + " to " + resultType);
				}
			} else if (operand.lrVal.getCType().isRealFloatingType()) {
				if (resultType.isIntegerType()) {
					convertFloatToInt(loc, operand, resultType);
				} else if (resultType.isRealFloatingType()) {
					convertFloatToFloat(loc, operand, resultType);
				} else {
					throw new UnsupportedSyntaxException(loc, "conversion from " + operand.lrVal.getCType() + " to " + resultType);
				}
			} else {
				throw new UnsupportedSyntaxException(loc, "conversion from " + operand.lrVal.getCType() + " to " + resultType);
			}
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
	 * Conversion from some integer type to some integer type which is not _Bool.
	 */
	public abstract void convertIntToInt_NonBool(ILocation loc, ExpressionResult operand, CPrimitive resultType);
	
	public final void convertIntToInt(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		if (newType.getType() == PRIMITIVE.BOOL) {
			convertToBool(loc, rexp);
		} else {
			convertIntToInt_NonBool(loc, rexp, newType);
		}
	}
	
	/**
	 * Perform the integer promotions a specified in C11 6.3.1.1.2 on the
	 * operand.
	 */
	public final void doIntegerPromotion(ILocation loc, ExpressionResult operand) {
		final CType ctype = CEnum.replaceEnumWithInt(operand.lrVal.getCType().getUnderlyingType());
		if (!(ctype instanceof CPrimitive)) {
			throw new IllegalArgumentException("integer promotions not applicable to " + ctype);
		}
		final CPrimitive cPrimitive = (CPrimitive) ctype;
		if (integerPromotionNeeded(cPrimitive)) {
			final CPrimitive promotedType = determineResultOfIntegerPromotion(cPrimitive);
			convertIntToInt(loc, operand, promotedType);
		}
	}
	
	private boolean integerPromotionNeeded(CPrimitive cPrimitive) {
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
	
		
	private CPrimitive determineResultOfIntegerPromotion(CPrimitive cPrimitive) {
		final int sizeOfArgument = mTypeSizes.getSize(cPrimitive.getType());
		final int sizeofInt = mTypeSizes.getSize(CPrimitive.PRIMITIVE.INT);
		
		if (sizeOfArgument < sizeofInt || !cPrimitive.isUnsigned()) {
			return new CPrimitive(PRIMITIVE.INT);
		} else {
			return new CPrimitive(PRIMITIVE.UINT);
		}
	}
	

	/**
	 * In our Lindenmann-Hoenicke memory model, a pointer is a struct of two
	 * integer data types. This method returns the CType of the structs
	 * components.
	 */
	public abstract CPrimitive getCTypeOfPointerComponents();

	public final void convertPointerToInt(ILocation loc, ExpressionResult rexp,
			CPrimitive newType) {
		mPointerIntegerConversion.convertPointerToInt(loc, rexp, newType);
	}

	
	protected String declareConversionFunctionOverApprox(ILocation loc, CPrimitive oldType, CPrimitive newType) {
		final String functionName = "convert" + oldType.toString() +"To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType resultASTType = mTypeHandler.ctype2asttype(loc, newType);
			final ASTType paramASTType = mTypeHandler.ctype2asttype(loc, oldType);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}
	
	abstract protected String declareConversionFunction(ILocation loc, CPrimitive oldType, CPrimitive newType);
	
	protected String declareBinaryFloatComparisonOperation(ILocation loc, CPrimitive type) {
		final String functionName = "someBinary" + type.toString() +"ComparisonOperation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType paramAstType = mTypeHandler.ctype2asttype(loc, type);
			final ASTType resultAstType = new PrimitiveType(loc, SFO.BOOL);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType, paramAstType, paramAstType);
		}
		return prefixedFunctionName;
	}
	
	private String declareBinaryArithmeticFloatOperation(ILocation loc, CPrimitive type) {
		final String functionName = "someBinaryArithmetic" + type.toString() +"operation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType astType = mTypeHandler.ctype2asttype(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType, astType);
		}
		return prefixedFunctionName;
	}
	
	private String declareUnaryFloatOperation(ILocation loc, CPrimitive type) {
		final String functionName = "someUnary" + type.toString() +"operation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType astType = mTypeHandler.ctype2asttype(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType);
		}
		return prefixedFunctionName;
	}
	
	public final void convertIntToPointer(ILocation loc, ExpressionResult rexp,
			CPointer newType) {
		mPointerIntegerConversion.convertIntToPointer(loc, rexp, newType);
	}
	

	
	public void convertFloatToInt(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		if (newType.getType() == PRIMITIVE.BOOL) {
			convertToBool(loc, rexp);
		} else {
			convertFloatToInt_NonBool(loc, rexp, newType);
		}
	}

	public void convertFloatToInt_NonBool(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
//		throw new UnsupportedSyntaxException(loc, "conversion from float to int not yet implemented");
		final String prefixedFunctionName = declareConversionFunction(loc, (CPrimitive) rexp.lrVal.getCType(), newType);
		final Expression oldExpression = rexp.lrVal.getValue();
		final IdentifierExpression roundingMode = new IdentifierExpression(null, "RTZ");
		roundingMode.setDeclarationInformation(new DeclarationInformation(StorageClass.GLOBAL, null));
		final Expression resultExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {roundingMode, oldExpression});
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.lrVal = rValue;
	}

	public void convertIntToFloat(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
//		throw new UnsupportedSyntaxException(loc, "conversion from int to float not yet implemented");
		final String prefixedFunctionName = declareConversionFunction(loc, (CPrimitive) rexp.lrVal.getCType(), newType);
		final Expression oldExpression = rexp.lrVal.getValue();
		final Expression resultExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {getRoundingMode(), oldExpression});
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.lrVal = rValue;

	}
	
	public void convertFloatToFloat(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
//		throw new UnsupportedSyntaxException(loc, "conversion from float to float not yet implemented");
		final String prefixedFunctionName = declareConversionFunction(loc, (CPrimitive) rexp.lrVal.getCType(), newType);
		final Expression oldExpression = rexp.lrVal.getValue();
		final Expression resultExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] { getRoundingMode(), oldExpression});
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.lrVal = rValue;
	}
	
	/**
	 * Convert any scalar type to _Bool. Section 6.3.1.2 of C11 says:
 	 * When any scalar value is converted to _Bool, the result is 0 if the value 
     * compares equal to 0; otherwise, the result is 1.
	 */
	void convertToBool(ILocation loc, ExpressionResult rexp) {
		CType underlyingType = rexp.lrVal.getCType();
		underlyingType = CEnum.replaceEnumWithInt(underlyingType);
		final Expression zeroInputType = constructZero(loc, underlyingType);
		final Expression isZero;
		if (underlyingType instanceof CPointer) {
			isZero = ExpressionFactory.newBinaryExpression(loc, 
					BinaryExpression.Operator.COMPEQ, rexp.lrVal.getValue(), zeroInputType);
		} else if (underlyingType instanceof CPrimitive) {
			isZero = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals, 
					rexp.lrVal.getValue(), (CPrimitive) underlyingType, 
					zeroInputType, (CPrimitive) underlyingType);
		} else {
			throw new UnsupportedOperationException("unsupported: conversion from " + underlyingType + " to _Bool");
		}
		final Expression zeroBool = constructLiteralForIntegerType(loc, new CPrimitive(PRIMITIVE.BOOL), BigInteger.ZERO);
		final Expression oneBool = constructLiteralForIntegerType(loc, new CPrimitive(PRIMITIVE.BOOL), BigInteger.ONE);
		final Expression resultExpression = ExpressionFactory.newIfThenElseExpression(loc, isZero, zeroBool, oneBool);
		final RValue rValue = new RValue(resultExpression, new CPrimitive(PRIMITIVE.BOOL), false, false);
		rexp.lrVal = rValue;
	}
	
	
	public abstract void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType ctype, List<Statement> stmt);
	
	
	public Expression constructNullPointer(ILocation loc) {
//		return new IdentifierExpression(loc, SFO.NULL);
		return constructPointerForIntegerValues(loc, BigInteger.ZERO, BigInteger.ZERO);
	}
	
	public Expression constructPointerForIntegerValues(ILocation loc, BigInteger baseValue, BigInteger offsetValue) {
		final Expression base = constructLiteralForIntegerType(loc, 
				getCTypeOfPointerComponents(), baseValue);
		final Expression offset = constructLiteralForIntegerType(loc, 
				getCTypeOfPointerComponents(), offsetValue);
		return MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc); 
	}
	
	public Expression constructZero(ILocation loc, CType cType) {
		final Expression result;
		if (cType instanceof CPrimitive) {
			switch (((CPrimitive) cType).getGeneralType()) {
			case FLOATTYPE:
				result = constructLiteralForFloatingType(loc,
						(CPrimitive) cType, BigInteger.ZERO);
				break;
			case INTTYPE:
				result = constructLiteralForIntegerType(loc, 
						(CPrimitive) cType, BigInteger.ZERO);
				break;
			case VOID:
				throw new UnsupportedSyntaxException(loc, "no 0 value of type VOID");
			default:
				throw new AssertionError("illegal type");
			}
		} else if (cType instanceof CPointer) {
			result = constructNullPointer(loc);
		} else {
			throw new UnsupportedSyntaxException(loc, "don't know 0 value for type " + cType);
		}
		return result;
	}

	/**
	 * Returns an {@link Expression} that represents the following bits of 
	 * operand high-1, high-2, ..., low+1, low (i.e., the bit at the higher 
	 * index is not included, the bit at the lower index is included).  
	 */
	public abstract Expression extractBits(ILocation loc, Expression operand, int high, int low);

	public abstract Expression concatBits(ILocation loc, List<Expression> dataChunks, int size);
	
	public abstract Expression signExtend(ILocation loc, Expression operand, int bitsBefore, int bitsAfter);
	
	public abstract ExpressionResult createNanOrInfinity(ILocation loc, String name);

	public abstract Expression getRoundingMode();
	
	public abstract Expression createFloatingPointClassificationFunction(ILocation loc, String name);
}
