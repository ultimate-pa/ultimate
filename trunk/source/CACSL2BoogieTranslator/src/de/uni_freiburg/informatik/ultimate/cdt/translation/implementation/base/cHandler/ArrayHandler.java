/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * Class that handles translation of arrays.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class ArrayHandler {
	
	private POINTER_CHECKMODE m_checkArrayAccessOffHeap;

	public ArrayHandler() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		m_checkArrayAccessOffHeap = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_ARRAYACCESSOFFHEAP, POINTER_CHECKMODE.class);
	}

	/**
	 * This stack stack collects ResultExpressions from subscripts. When going down
	 * into nested subscripts recursively a ResultExpression is pushed for each subscript.
	 * When going up again the ResultExpressions are popped/used.
	 */
	Stack<ExpressionResult> mCollectedSubscripts = new Stack<ExpressionResult>();
	
	
	public ExpressionResult handleArraySubscriptExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			IASTArraySubscriptExpression node) {		
		ILocation loc = LocationFactory.createCLocation(node);
		
		ExpressionResult subscript = (ExpressionResult) main.dispatch(node.getArgument());
		ExpressionResult subscriptR = subscript.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		mCollectedSubscripts.push(subscriptR);
		
		//have we arrived at the innermost array subscript? (i.e. a[i] instead of a[j][i])
		boolean innerMostSubscript = 
				!(node.getArrayExpression() instanceof IASTArraySubscriptExpression);
		ExpressionResult innerResult = null;
		if (innerMostSubscript) {
			innerResult = ((ExpressionResult) main.dispatch(node.getArrayExpression()));
		} else {
			innerResult = handleArraySubscriptExpression(main, memoryHandler, 
					structHandler, (IASTArraySubscriptExpression) node.getArrayExpression());
		}
		
		ExpressionResult result = new ExpressionResult(innerResult);
		
		ExpressionResult currentSubscriptRex = mCollectedSubscripts.pop();
		result.stmt.addAll(currentSubscriptRex.stmt);
		result.decl.addAll(currentSubscriptRex.decl);
		result.auxVars.putAll(currentSubscriptRex.auxVars);
		result.overappr.addAll(currentSubscriptRex.overappr);
		
		if (result.lrVal.getCType() instanceof CPointer) {
			//we have a pointer that is accessed like an array
			result = result.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			CType pointedType = ((CPointer) result.lrVal.getCType()).pointsToType;
			RValue address = ((CHandler) main.cHandler).doPointerArithPointerAndInteger(
					main, IASTBinaryExpression.op_plus, loc, 
					(RValue) result.lrVal, 
					(RValue) currentSubscriptRex.lrVal,
					pointedType);
			result.lrVal  = new HeapLValue(address.getValue(), pointedType);
		} else {
			assert result.lrVal.getCType().getUnderlyingType() instanceof CArray : "cType not instanceof CArray";
			ArrayList<Expression> newDimensions = 
					new ArrayList<Expression>(Arrays.asList(((CArray) result.lrVal.getCType().getUnderlyingType())
							.getDimensions()));
			CType newCType = null;
			if (newDimensions.size() == 1) {
				newCType = ((CArray) result.lrVal.getCType().getUnderlyingType()).getValueType();
			} else {
				newDimensions.remove(0);
				newCType = new CArray(newDimensions.toArray(new Expression[0]), 
						((CArray) result.lrVal.getCType().getUnderlyingType()).getValueType()
						);
			}

			if (result.lrVal instanceof HeapLValue) {
				result.lrVal = new HeapLValue(((CHandler) main.cHandler).doPointerArith(
						main, IASTBinaryExpression.op_plus, loc, 
						((HeapLValue) result.lrVal).getAddress(),
						currentSubscriptRex.lrVal.getValue(),
						newCType), newCType);
			} else if (result.lrVal instanceof LocalLValue) {
				LocalLValue newLLVal = new LocalLValue((LocalLValue) result.lrVal);
				LeftHandSide innerArrayLHS = ((LocalLValue) result.lrVal).getLHS();
				if (innerArrayLHS instanceof ArrayLHS) {
					ArrayList<Expression> innerIndices = new ArrayList<Expression>(
							Arrays.asList(((ArrayLHS) innerArrayLHS).getIndices()));
					innerIndices.add(currentSubscriptRex.lrVal.getValue());
					newLLVal.lhs = new ArrayLHS(loc, 
							((ArrayLHS) innerArrayLHS).getArray(), innerIndices.toArray(new Expression[0]));
				} else {
					newLLVal.lhs = new ArrayLHS(loc, 
							innerArrayLHS, new Expression[] { currentSubscriptRex.lrVal.getValue() });	
				}
				
				if (m_checkArrayAccessOffHeap == POINTER_CHECKMODE.ASSERTandASSUME
						|| m_checkArrayAccessOffHeap == POINTER_CHECKMODE.ASSUME) {
					Expression notTooBig = new BinaryExpression(loc, Operator.COMPLEQ, 
							new BinaryExpression(loc, Operator.ARITHMUL,
									currentSubscriptRex.lrVal.getValue(), 
									memoryHandler.calculateSizeOf(newCType, loc)),
									new BinaryExpression(loc, Operator.ARITHMINUS,
											memoryHandler.calculateSizeOf(innerResult.lrVal.getCType(), loc),
											memoryHandler.calculateSizeOf(newCType, loc)));
					Expression nonNegative = new BinaryExpression(loc, Operator.COMPGEQ,
							currentSubscriptRex.lrVal.getValue(),
							new IntegerLiteral(loc, "0"));
					Expression inRange = new BinaryExpression(loc, Operator.LOGICAND, 
							nonNegative, notTooBig);
					if (m_checkArrayAccessOffHeap == POINTER_CHECKMODE.ASSERTandASSUME) {
						Check check = new Check(Spec.ARRAY_INDEX);
						ILocation locationWithCheck = LocationFactory.createCLocation(node, check);
						result.stmt.add(new AssertStatement(locationWithCheck, inRange));
					}
					result.stmt.add(new AssumeStatement(loc, inRange));
				}
				
				newLLVal.setCType(newCType);
				result.lrVal = newLLVal;
			} else {
				throw new AssertionError("should not happen");
			}
		}
		
		return result;
	}
}
