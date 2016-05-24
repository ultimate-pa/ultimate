/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class OverapproximationUF implements IPointerIntegerConversion {
	
	protected final  AExpressionTranslation mExpressionTranslation;
	private final FunctionDeclarations mFunctionDeclarations;
	private final ITypeHandler mTypeHandler;
	

	/**
	 * Defines the following conversion between pointers and integers.
	 * An integer n is converted to the pointer with base address 0 and offset n.
	 * If a pointer is converted to an integer type, we use an uninterpreted
	 * function and we add the overapproximation flag to the resulting expression. 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */

	public OverapproximationUF(AExpressionTranslation expressionTranslation, FunctionDeclarations functionDeclarations,
			ITypeHandler typeHandler) {
		super();
		mExpressionTranslation = expressionTranslation;
		mFunctionDeclarations = functionDeclarations;
		mTypeHandler = typeHandler;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.IPointerIntConversion#convertPointerToInt(de.uni_freiburg.informatik.ultimate.model.location.ILocation, de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult, de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive)
	 */
	@Override
	public void convertPointerToInt(ILocation loc, ExpressionResult rexp,
			CPrimitive newType) {
		if (newType.getType() == PRIMITIVE.BOOL) {
			mExpressionTranslation.convertToBool(loc, rexp);
		} else {
			String prefixedFunctionName = declareConvertPointerToIntFunction(
					loc, newType);
			Expression pointerExpression = rexp.lrVal.getValue();
			Expression intExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {pointerExpression});
			RValue rValue = new RValue(intExpression, newType, false, false);
			rexp.lrVal = rValue;
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.IPointerIntConversion#convertIntToPointer(de.uni_freiburg.informatik.ultimate.model.location.ILocation, de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult, de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer)
	 */
	@Override
	public void convertIntToPointer(ILocation loc, ExpressionResult rexp,
			CPointer newType) {
		boolean overapproximate = false;
		if (overapproximate) {
			String prefixedFunctionName = declareConvertIntToPointerFunction(loc, (CPrimitive) rexp.lrVal.getCType());
			Expression intExpression = rexp.lrVal.getValue();
			Expression pointerExpression = new FunctionApplication(loc, prefixedFunctionName, new Expression[] {intExpression});
			RValue rValue = new RValue(pointerExpression, newType, false, false);
			rexp.lrVal = rValue;
		} else {
			mExpressionTranslation.convertIntToInt(loc, rexp, mExpressionTranslation.getCTypeOfPointerComponents());
			Expression zero = mExpressionTranslation.constructLiteralForIntegerType(
					loc, mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
			RValue rValue = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(zero, rexp.lrVal.getValue(), loc), newType, false, false);
			rexp.lrVal = rValue;
		}
	}
	
	private String declareConvertIntToPointerFunction(ILocation loc, CPrimitive newType) {
		String functionName = "convert" + newType.toString() + "toPointer";
		String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType resultASTType = mTypeHandler.constructPointerType(loc); 
			ASTType paramASTType = mTypeHandler.ctype2asttype(loc, newType);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}
	
	private String declareConvertPointerToIntFunction(ILocation loc, CPrimitive newType) {
		String functionName = "convertPointerTo" + newType.toString();
		String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType resultASTType = mTypeHandler.ctype2asttype(loc, newType);
			ASTType paramASTType = mTypeHandler.constructPointerType(loc);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}

}
