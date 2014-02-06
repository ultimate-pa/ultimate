package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFieldDesignator;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Class that handles translation of Structs.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 * modified (a lot) by Alexander Nutz in later 2013/early 2014
 */
public class StructHandler {

	/**
	 * Handle IASTFieldReference.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @param memoryHandler 
	 * @return the translation results.
	 */
	public Result handleFieldReference(Dispatcher main, IASTFieldReference node, MemoryHandler memoryHandler) {
		CACSLLocation loc = new CACSLLocation(node);
		String field = node.getFieldName().toString();
		
		ResultExpression fieldOwner = (ResultExpression) main.dispatch(node.getFieldOwner());;

		LRValue newValue = null;

		CType foType = fieldOwner.lrVal.cType;
		if (foType instanceof CNamed)
			foType = ((CNamed) foType).getUnderlyingType();
		foType = (node.isPointerDereference() ?
				((CPointer)foType).pointsToType :
					foType);
		CStruct cStructType = (CStruct) (foType instanceof CNamed ? ((CNamed) foType).getUnderlyingType() : foType);
		CType cFieldType = cStructType.getFieldType(field);

		if (node.isPointerDereference()) {
			ResultExpression rFieldOwnerRex = fieldOwner.switchToRValueIfNecessary(main, memoryHandler, this, loc);
			Expression address = rFieldOwnerRex.lrVal.getValue();
			fieldOwner = new ResultExpression(rFieldOwnerRex.stmt, new HeapLValue(address, rFieldOwnerRex.lrVal.cType), 
					rFieldOwnerRex.decl, rFieldOwnerRex.auxVars);
		}

		if (fieldOwner.lrVal instanceof HeapLValue) {
			HeapLValue fieldOwnerHlv = (HeapLValue) fieldOwner.lrVal;

			
			Expression startAddress = fieldOwnerHlv.getAddress();
			Expression newStartAddressBase = null;
			Expression newStartAddressOffset = null;
			if (startAddress instanceof StructConstructor) {
				newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
				newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
			} else {
				newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
				newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
			}
			Expression newPointer = MemoryHandler.constructPointerFromBaseAndOffset(
					newStartAddressBase,
					new BinaryExpression(loc, new InferredType(Type.Integer), BinaryExpression.Operator.ARITHPLUS, 
							newStartAddressOffset,
							getStructOffsetConstantExpression(loc, memoryHandler, field, cStructType)),
							loc);
			newValue = new HeapLValue(newPointer, cFieldType);
		} else if (fieldOwner.lrVal instanceof RValue) {
			RValue rVal = (RValue) fieldOwner.lrVal;
			StructAccessExpression sexpr = new StructAccessExpression(loc, 
					rVal.getValue(), field);
			newValue = new RValue(sexpr, cFieldType);
		} else { 
			LocalLValue lVal = (LocalLValue) fieldOwner.lrVal;
			StructLHS slhs = new StructLHS(loc,
					lVal.getLHS(), field);
			newValue = new LocalLValue(slhs, cFieldType);
		}
		return new ResultExpression(fieldOwner.stmt, newValue, fieldOwner.decl, fieldOwner.auxVars);
	}


	public Result readFieldInTheStructAtAddress(Dispatcher main,
			MemoryHandler memoryHandler, ILocation loc, String field,
			RValue address) {
		Expression addressBaseOfFieldOwner;
		Expression addressOffsetOfFieldOwner;
		
		Expression structAddress = address.getValue();
		CStruct structType = (CStruct) address.cType.getUnderlyingType();

		addressBaseOfFieldOwner = new StructAccessExpression(loc, 
				structAddress, SFO.POINTER_BASE);
		addressOffsetOfFieldOwner = new StructAccessExpression(loc, 
				structAddress, SFO.POINTER_OFFSET);

		if (structType == null || !(structType instanceof CStruct)) {
			String msg = "Incorrect or unexpected field owner!";
			throw new IncorrectSyntaxException(loc, msg);
		}
		IdentifierExpression additionalOffset = getStructOffsetConstantExpression(
				loc, memoryHandler, field, structType);
		Expression newOffset;
		if (isZero(addressOffsetOfFieldOwner)) {
			newOffset = additionalOffset;
		} else {
			newOffset = new BinaryExpression(loc, Operator.ARITHPLUS, 
					addressOffsetOfFieldOwner, additionalOffset);
		}
		StructConstructor newPointer = 
				MemoryHandler.constructPointerFromBaseAndOffset(addressBaseOfFieldOwner, newOffset, loc);

		CType resultType = structType.getFieldType(field);

		RValue newAddress = new RValue(address);
		newAddress.value = newPointer;
		newAddress.cType= resultType;
		
		ResultExpression call = 
				memoryHandler.getReadCall(main, 
					newAddress);	
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new HashMap<VariableDeclaration, ILocation>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		stmt.addAll(call.stmt);
		decl.addAll(call.decl);
		auxVars.putAll(call.auxVars);
		overappr.addAll(call.overappr);
		ResultExpression result = new ResultExpression(stmt,
		        new RValue(call.lrVal.getValue(), resultType), decl, auxVars,
		        overappr);
		return result;
	}

	public static IdentifierExpression getStructOffsetConstantExpression(
			ILocation loc, MemoryHandler memoryHandler, String fieldId, CType structCType) {
		String offset = SFO.OFFSET + structCType.toString() + "~" + fieldId;
		IdentifierExpression additionalOffset = new IdentifierExpression(loc, offset);
		memoryHandler.calculateSizeOf(structCType, loc);//needed such that offset constants are declared
		return additionalOffset;
	}

	/**
	 * Returns true iff expr is IntegerLiteral "0".
	 */
	private boolean isZero(Expression expr) {
		if (expr instanceof IntegerLiteral) {
			IntegerLiteral il = (IntegerLiteral) expr;
			return il.getValue().equals(SFO.NR0);
		} else {
			return false;
		}
	}

	/**
	 * Handle IASTDesignatedInitializer.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleDesignatedInitializer(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			CASTDesignatedInitializer node) {
		CACSLLocation loc = new CACSLLocation(node);
		assert node.getDesignators().length == 1;
		assert node.getDesignators()[0] instanceof CASTFieldDesignator;
		CASTFieldDesignator fr = (CASTFieldDesignator) node.getDesignators()[0];
		String id = fr.getName().getRawSignature();
		Result r = main.dispatch(node.getOperand());
		if (r instanceof ResultExpressionListRec) {
			ResultExpressionListRec relr = (ResultExpressionListRec) r;
			if (!relr.list.isEmpty()) {
				assert relr.stmt.isEmpty();
				//                assert relr.expr == null;//TODO??
				assert relr.lrVal == null;
				assert relr.decl.isEmpty();
				ResultExpressionListRec named = new ResultExpressionListRec(id);
				named.list.addAll(relr.list);
				return named;
			}
			return new ResultExpressionListRec(id, relr.stmt, relr.lrVal,
					relr.decl, relr.auxVars, relr.overappr).switchToRValueIfNecessary(
					        main, memoryHandler, structHandler, loc);
		} else if (r instanceof ResultExpression) {
			ResultExpression rex = (ResultExpression) r;
			return rex.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		} else {
			String msg = "Unexpected result";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public ResultExpression makeStructConstructorFromRERL(Dispatcher main, ILocation loc, MemoryHandler memoryHandler, ArrayHandler arrayHandler,
			FunctionHandler functionHandler, ResultExpressionListRec rerlIn, CStruct structType, boolean onHeap) {
		ResultExpressionListRec rerl = null;
		if (rerlIn == null)
			rerl = new ResultExpressionListRec();
		else
			rerl = rerlIn;
		
		if (rerl.lrVal != null) //we have an identifier (or sth else too?)
			return new ResultExpression(rerl.stmt, rerl.lrVal, rerl.decl,
			        rerl.auxVars, rerl.overappr);

		//everything for the new Result
		ArrayList<Statement> newStmt = new ArrayList<Statement>();
		ArrayList<Declaration> newDecl = new ArrayList<Declaration>();
		HashMap<VariableDeclaration, ILocation> newAuxVars =
		        new HashMap<VariableDeclaration, ILocation>();
		List<Overapprox> newOverappr = new ArrayList<Overapprox>();
		
		String[] fieldIds = structType.getFieldIds();
		CType[] fieldTypes = structType.getFieldTypes();

		//the new Arrays for the StructConstructor
		ArrayList<String> fieldIdentifiers = new ArrayList<String>();
		ArrayList<Expression> fieldValues = new ArrayList<Expression>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			CType underlyingFieldType;
			if (fieldTypes[i] instanceof CNamed)
				underlyingFieldType = ((CNamed) fieldTypes[i]).getUnderlyingType();
			else
				underlyingFieldType = fieldTypes[i];

			ResultExpression fieldContents = null; 
			if(underlyingFieldType instanceof CPrimitive) {
				if (i < rerl.list.size())
					fieldContents = rerl.list.get(i);
				else
					fieldContents = new ResultExpression(new RValue(
							new IntegerLiteral(loc, "0"), underlyingFieldType));
			} else if (underlyingFieldType instanceof CPointer) {
				if (i < rerl.list.size())
					fieldContents = rerl.list.get(i);
				else
					fieldContents = new ResultExpression(new RValue(
							MemoryHandler.constructNullPointer(loc), underlyingFieldType));
			} else if (underlyingFieldType instanceof CArray) {
				ArrayList<Statement> fieldStmt = new ArrayList<Statement>();
				ArrayList<Declaration> fieldDecl = new ArrayList<Declaration>();
				HashMap<VariableDeclaration, ILocation> fieldAuxVars =
						new HashMap<VariableDeclaration, ILocation>();
				
				String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYINIT);
				
				ResultExpressionListRec arrayInitRerl = null;
				if (i < rerl.list.size())
					arrayInitRerl = rerl.list.get(i);
				
				Expression fieldEx = new IdentifierExpression(loc, tmpId);
				RValue lrVal = new RValue(fieldEx, underlyingFieldType);
				//FIXME: off heap case missing
				if (onHeap) {			
					VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, MemoryHandler.POINTER_TYPE, loc);
					fieldAuxVars.put(tVarDecl, (CACSLLocation) loc);
					fieldDecl.add(tVarDecl);
					fieldStmt.addAll(arrayHandler.initArrayOnHeap(main, memoryHandler, this, loc, 
						arrayInitRerl == null ? null : arrayInitRerl.list, 
						fieldEx, functionHandler, (CArray) underlyingFieldType));
				} else {
					VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, 
							main.typeHandler.ctype2asttype(loc, underlyingFieldType),
							loc);
					fieldAuxVars.put(tVarDecl, (CACSLLocation) loc);
					fieldDecl.add(tVarDecl);
					VariableLHS fieldLHS = new VariableLHS(loc, tmpId);
					fieldStmt.addAll(arrayHandler.initBoogieArray(main, memoryHandler, this, functionHandler, loc, 
						arrayInitRerl == null ? null : arrayInitRerl.list, 
						fieldLHS, (CArray) underlyingFieldType));
				}
				fieldContents = new ResultExpression(fieldStmt, lrVal, fieldDecl, fieldAuxVars);
			} else if (underlyingFieldType instanceof CEnum) {
				throw new UnsupportedSyntaxException(loc, "..");
			} else if (underlyingFieldType instanceof CStruct) {
				if (i < rerl.list.size())
					fieldContents = makeStructConstructorFromRERL(main, loc, memoryHandler, arrayHandler, 
							functionHandler, rerl.list.get(i), (CStruct) underlyingFieldType, onHeap);
				else
					fieldContents = makeStructConstructorFromRERL(main, loc, memoryHandler, arrayHandler,
							functionHandler, new ResultExpressionListRec(), (CStruct) underlyingFieldType, onHeap);	
			} else if (underlyingFieldType instanceof CNamed) {
				assert false : "This should not be the case as we took the underlying type.";
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}	
			newStmt.addAll(fieldContents.stmt);
			newDecl.addAll(fieldContents.decl);
			newAuxVars.putAll(fieldContents.auxVars);
			newOverappr.addAll(fieldContents.overappr);
			assert fieldContents.lrVal instanceof RValue; //should be guaranteed by readFieldInTheStructAtAddress(..)
			fieldValues.add(((RValue) fieldContents.lrVal).getValue());
		}
		StructConstructor sc = new StructConstructor(loc, new InferredType(Type.Struct),
				fieldIdentifiers.toArray(new String[0]), 
				fieldValues.toArray(new Expression[0]));

		ResultExpression result = new ResultExpression(newStmt,
		        new RValue(sc, structType), newDecl, newAuxVars, newOverappr);
		return result;
	} 
}
