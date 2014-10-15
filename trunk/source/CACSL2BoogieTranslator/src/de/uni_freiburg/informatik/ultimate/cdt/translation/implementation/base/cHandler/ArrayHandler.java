package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;

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
	Stack<ResultExpression> mCollectedSubscripts = new Stack<ResultExpression>();
	
	
	public ResultExpression handleArraySubscriptExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			IASTArraySubscriptExpression node) {		
		ILocation loc = new CACSLLocation(node);
		
		ResultExpression subscript = (ResultExpression) main.dispatch(node.getArgument());
		ResultExpression subscriptR = subscript.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		mCollectedSubscripts.push(subscriptR);
		
		//have we arrived at the innermost array subscript? (i.e. a[i] instead of a[j][i])
		boolean innerMostSubscript = 
				!(node.getArrayExpression() instanceof IASTArraySubscriptExpression);
		ResultExpression innerResult = null;
		if (innerMostSubscript) {
			innerResult = ((ResultExpression) main.dispatch(node.getArrayExpression()));
		} else {
			innerResult = handleArraySubscriptExpression(main, memoryHandler, 
					structHandler, (IASTArraySubscriptExpression) node.getArrayExpression());
		}
		
		ResultExpression result = new ResultExpression(innerResult);
		
		ResultExpression currentSubscriptRex = mCollectedSubscripts.pop();
		result.stmt.addAll(currentSubscriptRex.stmt);
		result.decl.addAll(currentSubscriptRex.decl);
		result.auxVars.putAll(currentSubscriptRex.auxVars);
		result.overappr.addAll(currentSubscriptRex.overappr);
		
		if (result.lrVal.cType instanceof CPointer) {
			//we have a pointer that is accessed like an array
			result = result.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			CType pointedType = ((CPointer) result.lrVal.cType).pointsToType;
			RValue address = ((CHandler) main.cHandler).doPointerArithPointerAndInteger(
					main, IASTBinaryExpression.op_plus, loc, 
					(RValue) result.lrVal, 
					(RValue) currentSubscriptRex.lrVal,
					pointedType);
			result.lrVal  = new HeapLValue(address.getValue(), pointedType);
		} else {
			assert result.lrVal.cType instanceof CArray : "cType not instanceof CArray";
			ArrayList<Expression> newDimensions = 
					new ArrayList<Expression>(Arrays.asList(((CArray) result.lrVal.cType)
							.getDimensions()));
			CType newCType = null;
			if (newDimensions.size() == 1) {
				newCType = ((CArray) result.lrVal.cType).getValueType();
			} else {
				newDimensions.remove(0);
				newCType = new CArray(newDimensions.toArray(new Expression[0]), 
						((CArray) result.lrVal.cType).getValueType());
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
					Expression checkNotTooBig = new BinaryExpression(loc, Operator.COMPLEQ, 
							new BinaryExpression(loc, Operator.ARITHMUL,
									currentSubscriptRex.lrVal.getValue(), 
									memoryHandler.calculateSizeOf(newCType, loc)),
									new BinaryExpression(loc, Operator.ARITHMINUS,
											memoryHandler.calculateSizeOf(innerResult.lrVal.cType, loc),
											memoryHandler.calculateSizeOf(newCType, loc)));
					Expression checkNotNegative = new BinaryExpression(loc, Operator.COMPGEQ,
							currentSubscriptRex.lrVal.getValue(),
							new IntegerLiteral(loc, "0"));
					Expression check = new BinaryExpression(loc, Operator.LOGICAND, 
							checkNotNegative, checkNotTooBig);
					if (m_checkArrayAccessOffHeap == POINTER_CHECKMODE.ASSERTandASSUME)
						result.stmt.add(new AssertStatement(loc, check));
					result.stmt.add(new AssumeStatement(loc, check));
				}
				
				newLLVal.cType = newCType;
				result.lrVal = newLLVal;
			} else {
				throw new AssertionError("should not happen");
			}
		}
		
		return result;
	}
}
