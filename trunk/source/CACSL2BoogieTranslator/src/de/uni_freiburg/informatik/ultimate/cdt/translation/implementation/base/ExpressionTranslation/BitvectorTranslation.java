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
import java.util.Iterator;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
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
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION;

public class BitvectorTranslation extends AExpressionTranslation {
	
	private final boolean mOverapproximateFloatingPointOperations;
	private final Expression mRoundingMode;

	public BitvectorTranslation(TypeSizes mTypeSizeConstants, ITypeHandler typeHandler, 
			POINTER_INTEGER_CONVERSION pointerIntegerConversion, boolean overapproximateFloatingPointOperations) {
		super(mTypeSizeConstants, typeHandler, pointerIntegerConversion);
		mOverapproximateFloatingPointOperations = overapproximateFloatingPointOperations;
		final IdentifierExpression roundingMode = new IdentifierExpression(null, "RNE");
		roundingMode.setDeclarationInformation(new DeclarationInformation(StorageClass.GLOBAL, null));
		mRoundingMode = roundingMode;
	}

	@Override
	public ExpressionResult translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			final String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			final CPrimitive cprimitive = new CPrimitive(PRIMITIVE.CHAR);
			final int bitlength = 8 * mTypeSizes.getSize(PRIMITIVE.CHAR);
			return new ExpressionResult(new RValue(new BitvecLiteral(loc, val, bitlength), cprimitive));
		}
		default:
			return super.translateLiteral(main, node);
		}
	}
	
	@Override
	public RValue translateIntegerLiteral(ILocation loc, String val) {
		final RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, mTypeSizes);
		return rVal;
	}
	
	@Override
	public RValue translateFloatingLiteral(ILocation loc, String val) {
		declareFloatingPointConstructors(loc);
		final RValue rVal = ISOIEC9899TC3.handleFloatConstant(val, loc, true, mTypeSizes, mFunctionDeclarations, getRoundingMode());
		return rVal;
	}
	
	@Override
	public Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, true, mTypeSizes, type, value);
	}


	@Override
	public Expression constructBinaryComparisonIntegerExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		if(!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final Expression result;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals:
			result = constructBinaryEqualityExpression(loc, nodeOperator, exp1, type1, exp2, type2);
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
		if(!mFunctionDeclarations.checkParameters(type1, type2)) {
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
		declareBitvectorFunction(loc, functionName, functionName + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), true, new CPrimitive(PRIMITIVE.BOOL), null, type1, type2);
		final Expression result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});
		return result;
	}
	
	@Override
	public Expression constructBinaryBitwiseIntegerExpression(ILocation loc,
			int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight) {
		if(!mFunctionDeclarations.checkParameters(typeLeft, typeRight)) {
			throw new IllegalArgumentException("incompatible types " + typeLeft + " " + typeRight);
		}
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
			funcname = "bvand";
			break;
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
			funcname = "bvor";
			break;
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			funcname = "bvxor";
			break;
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftLeftAssign:
			funcname = "bvshl";
			break;
		case IASTBinaryExpression.op_shiftRight:
		case IASTBinaryExpression.op_shiftRightAssign:
			if (typeLeft.isUnsigned()) {
				funcname = "bvlshr";
			} else {
				funcname = "bvashr";
			}
			break;
		default:
			final String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, funcname, funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), false, typeLeft, null, typeLeft, typeRight);
		final Expression func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), new Expression[]{left, right});
		return func;
	}
	
	@Override
	public Expression constructUnaryIntegerExpression(ILocation loc,
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
			final String msg = "Unknown or unsupported unary expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, funcname, funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type), false, type, null, type);
		final Expression func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type), new Expression[]{expr});
		return func;
	}
	
	@Override
	public Expression constructArithmeticIntegerExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		FunctionApplication func;
		if(!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final String funcname;
		switch (nodeOperator) {
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
			if (type1.isUnsigned() && type2.isUnsigned()) {
				funcname = "bvudiv";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
				funcname = "bvsdiv";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			if (type1.isUnsigned() && type2.isUnsigned()) {
				funcname = "bvurem";
			} else if (!type1.isUnsigned() && !type2.isUnsigned()) {
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
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		
		declareBitvectorFunction(loc, funcname, funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), false, type1, null, type1, type2);
		func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), new Expression[]{exp1, exp2});

		return func;
	}

	private void declareBitvectorFunction(ILocation loc, String smtlibFunctionName, String boogieFunctionName,
			boolean boogieResultTypeBool, CPrimitive resultCType, int[] indices, CPrimitive... paramCType) {
		if (mFunctionDeclarations.getDeclaredFunctions().containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			// function already declared
			return;
		}
		final Attribute[] attributes = generateAttributes(loc, smtlibFunctionName, indices);
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes, boogieResultTypeBool, resultCType, paramCType);
	}

	private void declareFloatingPointFunction(ILocation loc, String smtlibFunctionName, String boogieFunctionName,
			boolean boogieResultTypeBool, boolean isRounded, CPrimitive resultCType, int[] indices, CPrimitive... paramCType) {
		if (mFunctionDeclarations.getDeclaredFunctions().containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			// function already declared
			return;
		}
		if (isRounded) {
			final ASTType[] paramASTTypes = new ASTType[paramCType.length + 1];
			final ASTType resultASTType = mTypeHandler.ctype2asttype(loc, resultCType);
			int counter = 1;
			paramASTTypes[0] = new NamedType(loc,"RoundingMode", new ASTType[0]);
			for (final CPrimitive cType : paramCType) {
				paramASTTypes[counter] = mTypeHandler.ctype2asttype(loc, cType);
				counter += 1;
			}
			final Attribute[] attributes = generateAttributes(loc, smtlibFunctionName, indices);
			mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes, resultASTType, paramASTTypes);
		}  else {
			final Attribute[] attributes = generateAttributes(loc, smtlibFunctionName, indices);
			mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes, boogieResultTypeBool, resultCType, paramCType);
		}
	}
	
	private void declareFloatingPointConstructors(ILocation loc) {
		final ASTType[] paramASTTypes = new ASTType[2];
		
		CPrimitive result = new CPrimitive(PRIMITIVE.FLOAT);
		ASTType resultASTType = mTypeHandler.ctype2asttype(loc, result);
		Attribute[] attributes = generateAttributes(loc, "to_fp", new int[]{8, 24});
		paramASTTypes[0] = new NamedType(loc, "RoundingMode", new ASTType[0]);
		paramASTTypes[1] = new PrimitiveType(loc, SFO.REAL);
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "declareFloat", attributes, resultASTType, paramASTTypes);
		
		result = new CPrimitive(PRIMITIVE.DOUBLE);
		attributes = generateAttributes(loc, "to_fp", new int[]{11, 53});
		resultASTType = mTypeHandler.ctype2asttype(loc, result);
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "declareDouble", attributes, resultASTType, paramASTTypes);
		
		result = new CPrimitive(PRIMITIVE.LONGDOUBLE);
		attributes = generateAttributes(loc, "to_fp", new int[]{15, 113});
		resultASTType = mTypeHandler.ctype2asttype(loc, result);
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + "declareLongDouble", attributes, resultASTType, paramASTTypes);
	}
	/**
	 * Generate the attributes for the Boogie code that make sure that we
	 * translate to the desired SMT functions.
	 */
	private Attribute[] generateAttributes(ILocation loc, String smtlibFunctionName, int[] indices) {
		Attribute[] attributes;
		if (indices == null) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[] { new StringLiteral(loc, smtlibFunctionName) });
		    attributes = new Attribute[] { attribute };
		} else {
		    final Expression[] literalIndices = new IntegerLiteral[indices.length];
		    for (int i = 0; i < indices.length; ++i) {
		    	literalIndices[i] = new IntegerLiteral(loc, String.valueOf(indices[i]));
		    }
		    final Attribute attribute1 = new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER, new Expression[] { new StringLiteral(loc, smtlibFunctionName) });
		    final Attribute attribute2 = new NamedAttribute(loc, FunctionDeclarations.s_INDEX_IDENTIFIER, literalIndices);
		    attributes = new Attribute[] { attribute1, attribute2 };
		}
		return attributes;
	}

	@Override
	public void convertIntToInt_NonBool(ILocation loc, ExpressionResult operand, CPrimitive resultType) {
		if (!(resultType instanceof CPrimitive)) {
			throw new UnsupportedOperationException("non-primitive types not supported yet " + resultType);
		}
		final CPrimitive resultPrimitive = resultType;
		if (!(resultPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE)) {
			throw new UnsupportedOperationException("non-integer types not supported yet " + resultType);
		}
		
		final int resultLength = mTypeSizes.getSize(resultPrimitive.getType()) * 8;
		final int operandLength = mTypeSizes.getSize(((CPrimitive) operand.lrVal.getCType()).getType()) * 8;
		
		if (resultLength == operandLength) {
			final RValue oldRValue = (RValue) operand.lrVal;
			final RValue rVal = new RValue(oldRValue.getValue(), resultType, 
					oldRValue.isBoogieBool(), oldRValue.isIntFromPointer());
			operand.lrVal = rVal;
		} else if (resultLength > operandLength) {
			extend(loc, operand, resultType, resultPrimitive, resultLength,
					operandLength);
		} else {
			final Expression bv = extractBits(loc, operand.lrVal.getValue(), resultLength, 0);
			final RValue rVal = new RValue(bv, resultType);
			operand.lrVal = rVal;
		}
	}


	@Override
	public Expression extractBits(ILocation loc, Expression operand, int high, int low) {
		final Expression bv = new BitVectorAccessExpression(loc, operand, high, low);
		return bv;
	}

	private void extend(ILocation loc, ExpressionResult operand, CType resultType, CPrimitive resultPrimitive, int resultLength, int operandLength) {
		final int[] indices = new int[]{resultLength - operandLength};
		String smtlibFunctionName;
		if (((CPrimitive) operand.lrVal.getCType()).isUnsigned()) {
			smtlibFunctionName = "zero_extend";
		} else {
			smtlibFunctionName = "sign_extend";
		}
		final String funcName = smtlibFunctionName + "From" + mFunctionDeclarations.computeBitvectorSuffix(loc, (CPrimitive) operand.lrVal.getCType())
		                             + "To" + mFunctionDeclarations.computeBitvectorSuffix(loc, resultPrimitive);
		declareBitvectorFunction(loc, smtlibFunctionName, funcName, false, resultPrimitive, indices, (CPrimitive) operand.lrVal.getCType());
		final FunctionApplication func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcName, new Expression[]{operand.lrVal.getValue()});
		final RValue rVal = new RValue(func, resultType);
		operand.lrVal = rVal;
	}

	@Override
	public BigInteger extractIntegerValue(Expression expr, CType cType) {
		if (cType.isIntegerType()) {
			cType = CEnum.replaceEnumWithInt(cType);
			if (expr instanceof BitvecLiteral) {
				final BigInteger value =  new BigInteger(((BitvecLiteral) expr).getValue());
				if (((CPrimitive) cType).isUnsigned()) {
					if (value.signum() < 0) {
						throw new UnsupportedOperationException("negative value");
					}
					return value;
				} else {
					return value;
				}
			} else {
				return null;
			}
		} else {
			return null;
		}
	}
	
	
	@Override
	public CPrimitive getCTypeOfPointerComponents() {
		// 2015-10-29 Matthias: using int is unsound on 64bit systems, but it 
		// probably saves a lot of conversions and I guess this unsoundness
		// is never a problem in the SV-COMP and most other code
		return new CPrimitive(PRIMITIVE.INT);
	}

	@Override
	public void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType ctype, List<Statement> stmt) {
		// do nothing. not needed for bitvectors
		
	}

	@Override
	public Expression concatBits(ILocation loc, List<Expression> dataChunks, int size) {
		Expression result;
		final Iterator<Expression> it = dataChunks.iterator();
		result = it.next();
		while (it.hasNext()) {
			final Expression nextChunk = it.next();
			result = ExpressionFactory.newBinaryExpression(loc, 
				BinaryExpression.Operator.BITVECCONCAT, 
				result, 
				nextChunk);
		}
		return result;
	}

	@Override
	public Expression signExtend(ILocation loc, Expression operand, int bitsBefore, int bitsAfter) {
		final ASTType resultType = ((TypeHandler) mTypeHandler).bytesize2asttype(loc, GENERALPRIMITIVE.INTTYPE, bitsAfter/8);
		final ASTType inputType = ((TypeHandler) mTypeHandler).bytesize2asttype(loc, GENERALPRIMITIVE.INTTYPE, bitsBefore/8);
		final String smtlibFunctionName = "sign_extend";
		final String boogieFunctionName = smtlibFunctionName + "From" + bitsBefore + "To" + bitsAfter;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			final int[] indices = new int[]{bitsAfter - bitsBefore};
			final Attribute[] attributes = generateAttributes(loc, smtlibFunctionName, indices);
			mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes, resultType, inputType);
		}
		return new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, new Expression[]{ operand });
	}

	@Override
	public Expression constructBinaryComparisonFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		if(!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		
		Expression result;
		boolean isNegated = false;
		final String funcname;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			funcname = "fp.eq";
			break;
		case IASTBinaryExpression.op_notequals:
			funcname = "fp.eq";
			isNegated = true;
			break;			
		case IASTBinaryExpression.op_greaterEqual:
			funcname = "fp.geq";
			break;
		case IASTBinaryExpression.op_greaterThan:
			funcname = "fp.gt";
			break;
		case IASTBinaryExpression.op_lessEqual:
			funcname = "fp.leq";
			break;
		case IASTBinaryExpression.op_lessThan:
			funcname = "fp.lt";
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}
		
		declareFloatingPointFunction(loc, funcname, funcname + type1.toString(), true, false, new CPrimitive(PRIMITIVE.BOOL), null, type1, type2);
		//TODO: evaluate possiblities for boogiefunctionnames
		result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + type1.toString(), new Expression[]{exp1, exp2});
		
		if (isNegated) {
			result = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, result);
		}
		return result;
	}

	@Override
	public Expression constructUnaryFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type) {
		final Expression result;
		final String funcname;
		switch (nodeOperator) {
		case IASTUnaryExpression.op_minus:
			funcname = "fp.neg";
			break;
		default:
			final String msg = "Unknown or unsupported unary expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareFloatingPointFunction(loc, funcname, funcname + type.toString(), false, false, type, null, type);
		result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + type.toString(), new Expression[]{exp});
		return result;
	}

	@Override
	public Expression constructArithmeticFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		FunctionApplication result;
		if(!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		boolean isRounded = true;
		final String funcname;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			funcname = "fp.sub";
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			funcname = "fp.mul";
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			funcname = "fp.div";
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			funcname = "fp.rem";
			isRounded = false;
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			funcname = "fp.add";
			break;
		default:
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		if (isRounded) {
			declareFloatingPointFunction(loc, funcname, funcname + type1.toString(), false, isRounded, type1, null, type1, type2);
			result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname + type1.toString(), new Expression[]{getRoundingMode(), exp1, exp2});
		} else {
			declareFloatingPointFunction(loc, funcname, funcname, false, isRounded, type1, null, type1, type2);
			result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, new Expression[]{exp1, exp2});
		}
		return result;
	}

	@Override
	public Expression constructBinaryEqualityExpression_Floating(ILocation loc, int nodeOperator, Expression exp1,
			CType type1, Expression exp2, CType type2) {
		return constructBinaryComparisonFloatingPointExpression(loc, nodeOperator, exp1, (CPrimitive) type1, exp2, (CPrimitive) type2);
	}

	@Override
	public Expression constructBinaryEqualityExpression_Integer(ILocation loc, int nodeOperator, Expression exp1,
			CType type1, Expression exp2, CType type2) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, exp1, exp2);
			} else 	if (nodeOperator == IASTBinaryExpression.op_notequals) {
				return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, exp1, exp2);
			} else {
				throw new IllegalArgumentException("operator is neither equals nor not equals");
			}
	}

	@Override
	protected String declareConversionFunction(ILocation loc, CPrimitive oldType, CPrimitive newType) {
		
		if (mOverapproximateFloatingPointOperations) {
			return declareConversionFunctionOverApprox(loc, oldType, newType);
		}
		
		final String functionName = "convert" + oldType.toString() +"To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			
			Attribute[] attributes = null;
			final ASTType paramASTType = mTypeHandler.ctype2asttype(loc, oldType);
			ASTType[] params;
			final ASTType roundingMode = new NamedType(loc,"RoundingMode", new ASTType[0]);
			if (newType.isFloatingType()) {
				final int[] indices = new int[2];
				if (newType.getType().equals(CPrimitive.PRIMITIVE.FLOAT)) {
					indices[0] = 8;
					indices[1] = 24;
				}
				if (newType.getType().equals(CPrimitive.PRIMITIVE.DOUBLE)) {
					indices[0] = 11;
					indices[1] = 53;
				}
				if (newType.getType().equals(CPrimitive.PRIMITIVE.LONGDOUBLE)) {
					indices[0] = 15;
					indices[1] = 113;
				}
				attributes = generateAttributes(loc, "to_fp", indices);
			} else {
				if (newType.getType().equals(CPrimitive.PRIMITIVE.INT)) {
					attributes = generateAttributes(loc, "fp.to_sbv", new int[] { 32 });
				} else if (newType.getType().equals(CPrimitive.PRIMITIVE.LONG) || newType.getType().equals(CPrimitive.PRIMITIVE.LONGLONG)) {
					attributes = generateAttributes(loc, "fp.to_sbv", new int[] { 64 });
				} else if (newType.getType().equals(CPrimitive.PRIMITIVE.UINT)) {
					attributes = generateAttributes(loc, "fp.to_ubv", new int[] { 32 });
				} else if (newType.getType().equals(CPrimitive.PRIMITIVE.ULONG) || newType.getType().equals(CPrimitive.PRIMITIVE.ULONGLONG)) {
					attributes = generateAttributes(loc, "fp.to_ubv", new int[] { 64 });
				}
			}
			params = new ASTType[]{roundingMode, paramASTType};
			final ASTType resultASTType = mTypeHandler.ctype2asttype(loc, newType);
			
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, params);
		}
		return prefixedFunctionName;
	}
	@Override
	public ExpressionResult createNanOrInfinity(ILocation loc, String name) {
		final String functionName;
		final String suffixedFunctionName;
		final String typeName;
		final String exponent;
		final String significant;
		if (name.equals("NAN") || name.equals("nan")) {
			functionName = "NaN";
			suffixedFunctionName = "NaN_d";
			typeName = "C_DOUBLE";
			exponent = "11";
			significant = "53";
		} else if (name.equals("INFINITY") || name.equals("inf") || name.equals("inff")) {
			functionName = "+oo";
			suffixedFunctionName = "+oo_d";
			typeName = "C_DOUBLE";
			exponent = "11";
			significant = "53";
		} else if (name.equals("nanl")){
			functionName = "NaN";
			suffixedFunctionName = "NaN_l";
			typeName = "C_LONGDOUBLE";
			exponent = "15";
			significant = "113";
		} else if (name.equals("nanf")){
			functionName = "NaN";
			suffixedFunctionName = "NaN_f";
			typeName = "C_FLOAT";
			exponent = "5";
			significant = "11";
		} else {
			throw new IllegalArgumentException("not a nan or infinity type");
		}
		final Expression[] indices = new Expression[]{new IntegerLiteral(loc, exponent), new IntegerLiteral(loc, significant)};
		final Attribute[] attributes = new Attribute []{ new NamedAttribute(loc, FunctionDeclarations.s_BUILTIN_IDENTIFIER,
				new Expression[]{new StringLiteral(loc, functionName)}), new NamedAttribute(loc, FunctionDeclarations.s_INDEX_IDENTIFIER, indices)};  
		final ASTType asttype = new NamedType(loc, typeName, new ASTType[0]);
		final ASTType paramType = new PrimitiveType(loc, SFO.INT);
		getFunctionDeclarations().declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + suffixedFunctionName, attributes, asttype, paramType, paramType);
		
		final FunctionApplication func = 	new FunctionApplication(loc,  SFO.AUXILIARY_FUNCTION_PREFIX + suffixedFunctionName, indices);
		return new ExpressionResult(new RValue(func, new CPrimitive(PRIMITIVE.FLOAT)));
	}

	@Override
	public Expression getRoundingMode() {
		return mRoundingMode;
	}
}
