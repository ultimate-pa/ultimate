package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTLiteralExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CArrayType;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * Class that handles translation of arrays.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class ArrayHandler {

	public ResultExpression handleArrayDeclarationOnHeap(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			FunctionHandler functionHandler, HashMap<Declaration, CType> globalVariables,
			HashMap<Declaration, ArrayList<Statement>> globalVariablesInits,
			IASTArrayDeclarator d, IASTDeclSpecifier iastDeclSpecifier, ResultTypes resType, String bId, CACSLLocation loc) {

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		HashMap<VariableDeclaration, CACSLLocation> auxVars =
				new HashMap<VariableDeclaration, CACSLLocation>();
		LRValue arrayPointer = null;

		ArrayList<Expression> sizeConstants = new ArrayList<Expression>();
		Expression overallSize = new IntegerLiteral(loc, new InferredType(Type.Integer), "1");
		for (IASTArrayModifier am : d.getArrayModifiers()) {
			ResultExpression constEx = (ResultExpression) main.
					dispatch(am.getConstantExpression());
			constEx = constEx.switchToRValue(main, //just to be safe..
					memoryHandler, structHandler, loc);
//			assert constEx.lrVal instanceof RValue : "we only allow arrays of constant size";
			sizeConstants.add(constEx.lrVal.getValue());
//			Integer constAsInt =  Integer.parseInt(((IntegerLiteral) constEx.lrVal.getValue()).getValue());
			overallSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
					overallSize, constEx.lrVal.getValue(), loc);//
		}

		Expression sizeOfCell = memoryHandler.calculateSizeOf(resType.cvar);
		CArray arrayType = new CArray(iastDeclSpecifier,  //TODO: think about this type things
				sizeConstants.toArray(new Expression[0]), resType.cvar);
		LocalLValue arrayId = new LocalLValue(new VariableLHS(loc, new InferredType(Type.Pointer), bId), arrayType);

		//handle initialization
		if (d.getInitializer() != null) {			
			//malloc the space on the heap for the array
			ResultExpression mallocCall = null;
			Expression mallocSize = null;
			mallocSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
					overallSize,
					sizeOfCell,
					loc);
			mallocCall = memoryHandler.getMallocCall(main, functionHandler, 
					mallocSize, loc);	
			stmt.addAll(mallocCall.stmt);
			decl.addAll(mallocCall.decl);
			auxVars.putAll(mallocCall.auxVars);
			arrayPointer = mallocCall.lrVal;
			arrayPointer.cType = arrayType;
			
			Statement assingPtrToArray = new AssignmentStatement(loc, 
					new LeftHandSide[]{ arrayId.getLHS() }, 
					new Expression[]{ arrayPointer.getValue() });
			stmt.add(assingPtrToArray);
			
			//evaluate the initializer and fill the heapspace of the array
			ResultExpressionListRec init = (ResultExpressionListRec) main.dispatch(d.getInitializer());
			ArrayList<Statement> arrayWrites = initArray(memoryHandler, structHandler, loc, init.list, 
					arrayId.getValue(), sizeOfCell, (CArray) arrayPointer.cType);
			stmt.addAll(arrayWrites);

			if (functionHandler.getCurrentProcedureID() != null) {
				for (String t : new String[] { SFO.INT, SFO.POINTER,
						SFO.REAL, SFO.BOOL }) {
					functionHandler.getModifiedGlobals()
					.get(functionHandler.getCurrentProcedureID())
					.add(SFO.MEMORY + "_" + t);
				}
			} else { //our initialized array belongs to a global variable
				//TODO -- handle globals?? or is it done via the symbolTable?? what with statics??
			}
		}
		return new ResultExpression(stmt, arrayId, decl, auxVars);
//		return new ResultExpression(stmt, arrayId, decl, auxVars);
	}

	//	FIXME: a little inconsistent: here, we assume non-variable, simple sizeConstants while not doing so at arraySubscriptExs
	private ArrayList<Statement> initArray(MemoryHandler memoryHandler, StructHandler structHandler, ILocation loc, 
			ArrayList<ResultExpressionListRec> list, Expression startAddress, Expression sizeOfCell, 
			CArray arrayType) {
		ArrayList<Statement> arrayWrites = new ArrayList<Statement>();
		
//		Integer currentSizeInt = sizeConstantsAsInt.get(depth);
		Expression[] dimensions = arrayType.getDimensions();
		Integer currentSizeInt = null;
		try {
			currentSizeInt = Integer.parseInt(((IntegerLiteral) dimensions[0]).getValue());
		} catch (NumberFormatException nfe) {
			throw new UnsupportedSyntaxException("trying to initialize an array whose size we don't know");
		}

		Expression newStartAddressBase = null;
		Expression newStartAddressOffset = null;
		if (startAddress instanceof StructConstructor) {
			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}

//		if (depth == dimensions.size() - 1) {
		if (dimensions.length == 1) {
			RValue val = null;

			for (int i = 0; i < currentSizeInt; i++) {
				if (list.size() > i) {
					if (list.get(i).lrVal == null) { //TODO: we may need to pass statements, decls, ...
						assert arrayType.getValueType() instanceof CStruct;
						val = (RValue) structHandler.makeStructConstructorFromRERL(loc, list.get(i), (CStruct) arrayType.getValueType()).lrVal;
					} else
						val = (RValue) list.get(i).lrVal; //if not enough values are given, fill the rest with the last
				}


				Expression writeOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
						new IntegerLiteral(null, new InferredType(Type.Integer), new Integer(i).toString()), 
						sizeOfCell,
						null);	
				writeOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
						newStartAddressOffset,
						writeOffset, 
						loc);

				Expression writeLocation = MemoryHandler.constructPointerFromBaseAndOffset(
						newStartAddressBase,
						writeOffset, 
						loc);

				arrayWrites.addAll(memoryHandler.getWriteCall(new HeapLValue(writeLocation, null), val));
			}
		} else {
			for (int i = 0; i < currentSizeInt; i++) { 
				Expression newStartAddressOffsetInner = newStartAddressOffset;

				Expression blockOffset = sizeOfCell;
				for (int j = 1; j < dimensions.length; j++) {
					blockOffset = 
							CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
									dimensions[j],
									blockOffset,
									loc);
				}
				blockOffset = 
						CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
								new IntegerLiteral(loc, new InferredType(Type.Integer), new Integer(i).toString()),
								blockOffset,
								loc);	
				newStartAddressOffsetInner = 
						CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
								newStartAddressOffsetInner,
								blockOffset,
								loc);	
				
				ArrayList<Expression> innerDims = new ArrayList<Expression>(Arrays.asList(arrayType.getDimensions()));
				innerDims.remove(0);//TODO ??
				CArray innerArrayType = new CArray(arrayType.getDeclSpec(), innerDims.toArray(new Expression[0]), 
						arrayType.getValueType());

				arrayWrites.addAll(
						initArray(memoryHandler, structHandler, loc, list.get(i).list,
								MemoryHandler.constructPointerFromBaseAndOffset(
										newStartAddressBase,
										newStartAddressOffsetInner, 
										loc),
										sizeOfCell, innerArrayType)); 
			}
		}
		return arrayWrites;
	}

	public Result handleArrayOnHeapSubscriptionExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			IASTArraySubscriptExpression node) {
		ILocation loc = new CACSLLocation(node);
		ResultExpression subscript = (ResultExpression) main.dispatch(node.getArgument());
		ResultExpression array = (ResultExpression) main.dispatch(node.getArrayExpression());
		
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		HashMap<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();


		ResultExpression subscriptR = subscript.switchToRValue(main, memoryHandler, structHandler, loc);
		stmt.addAll(subscript.stmt);
		decl.addAll(subscript.decl);
		auxVars.putAll(subscript.auxVars);
			
		//catch the case where we are doing a subscript on a pointer
		if (array.lrVal.cType instanceof CPointer) {
			ResultExpression arrayR = array.switchToRValue(main, memoryHandler, structHandler, loc);
			stmt.addAll(arrayR.stmt);
			decl.addAll(arrayR.decl);
			auxVars.putAll(arrayR.auxVars);
			
			RValue newPointer = ((CHandler) main.cHandler).doPointerArith(main, IASTBinaryExpression.op_plus, loc, 
					(RValue) arrayR.lrVal, (RValue) subscriptR.lrVal);
			HeapLValue newHlv = new HeapLValue(newPointer.getValue(), ((CPointer) array.lrVal.cType).pointsToType);
			return new ResultExpression(stmt, newHlv, decl, auxVars);
		}
		
		// we really have an array
		CArray arrayCType = (CArray) array.lrVal.cType;

		ArrayList<Expression> newDimensions = new ArrayList<Expression>(Arrays.asList(arrayCType.getDimensions()));
		newDimensions.remove(0);//FIXME: first or last??
		CType newCType = null;
		if (newDimensions.size() == 0)
			newCType = arrayCType.getValueType();
		else
			newCType = new CArray(
				arrayCType.getDeclSpec(), newDimensions.toArray(new Expression[0]), arrayCType.getValueType());
	

		Expression offset = subscriptR.lrVal.getValue();
		offset = computeSubscriptMultiplier(main, memoryHandler, loc,
				arrayCType, offset);	

		Expression arrayBase = null;
		Expression arrayOffset = null;
		if (node.getArrayExpression() instanceof IASTArraySubscriptExpression) {
			stmt.addAll(array.stmt);
			decl.addAll(array.decl);
			auxVars.putAll(array.auxVars);
			
			HeapLValue arrayHlv = (HeapLValue) array.lrVal;
			StructConstructor ptr = (StructConstructor) arrayHlv.getAddress();
			arrayBase = ptr.getFieldValues()[0];
			arrayOffset = ptr.getFieldValues()[1];
		} else{
			ResultExpression arrayR = array.switchToRValue(main, memoryHandler, structHandler, loc);
			stmt.addAll(arrayR.stmt);
			decl.addAll(arrayR.decl);
			auxVars.putAll(arrayR.auxVars);
	
			Expression arrayAddress = arrayR.lrVal.getValue();
			arrayBase = MemoryHandler.getPointerBaseAddress(arrayAddress, loc);
			arrayOffset = MemoryHandler.getPointerOffset(arrayAddress, loc);
		}

		offset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
				arrayOffset,
				offset, 
				loc);	

		Expression newPointer = MemoryHandler
				.constructPointerFromBaseAndOffset(arrayBase, offset, loc);

		return new ResultExpression(stmt, new HeapLValue(newPointer, newCType), decl, auxVars);
	}

	private Expression computeSubscriptMultiplier(Dispatcher main,
			MemoryHandler memoryHandler, ILocation loc, CArray arrayCType,
			Expression offset) {
		for (int i = 1; i < arrayCType.getDimensions().length; i++) {
			offset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
					offset, 
					arrayCType.getDimensions()[i], 
					loc);
		}
		offset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
				offset, 
				memoryHandler.calculateSizeOf(arrayCType.getValueType()), 
				loc);
		return offset;
	}
}
