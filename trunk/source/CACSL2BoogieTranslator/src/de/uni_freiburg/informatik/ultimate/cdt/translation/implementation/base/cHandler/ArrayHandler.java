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

    /**
     * Method to translate array initializer lists in assignments to an array.
     * 
     * @param main
     *            the main dispatcher
     * @param structHandler
     *            a reference to the struct handler.
     * @param loc
     *            the Location of the declaration of this array.
     * @param at
     *            the array type.
     * @param cvar
     *            the corresponding C Variable description.
     * @param lhs
     *            the array to initialize.
     * @param relr
     *            the initializer-list tree
     * @param indices
     *            an array initially {-1, -1, ..., -1}, with length = number of
     *            element of level 1 in the array.
     * @param pos
     *            initially -1. The current dimension.
     * @return a list of assert and assign statements. Maybe there are also some
     *         declarations of temp. vars.
     */
    public ResultExpression handleArrayInit(Dispatcher main, MemoryHandler memoryHandler,
            StructHandler structHandler, final CACSLLocation loc, ArrayType at,
            CArray cvar, final LeftHandSide lhs, ResultExpressionListRec relr,
            int[] indices, int pos) {
        // TODO : seems to be missing the initialization of arrays of structs,
        // where the structs are declared before:
        // struct point pt0 = { 2, 3 };
        // struct point pt1 = { 0, 1};
        // struct point points[2] = {pt0, pt1};
        // results in:
        // assert (0 < 2 && 2 > 0) && 0 >= 0;
        // ~points~2[0]!x := ~pt0~2; // TODO : wrong!
        // assert (1 < 2 && 2 > 0) && 1 >= 0;
        // ~points~2[1]!x := ~pt1~2; // TODO : wrong!
        // the !x should be omitted in this case, or the structs on the rhs need
        // to be expanded!
        ASTType valueType = at.getValueType();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
		
		relr = relr.switchToRValue(main, memoryHandler, structHandler, loc);
		
        if (relr.list == null) {
            if (relr.decl != null)
                decl.addAll(relr.decl);
            if (relr.stmt != null)
                stmt.addAll(relr.stmt);
            if (relr.lrVal != null) {
                // relr.expr -> assert + assign!
                Expression[] idc = new Expression[indices.length];
                for (int i = 0; i < indices.length; i++)
                    idc[i] = new IntegerLiteral(loc, new InferredType(
                            Type.Integer), indices[i] + SFO.EMPTY);

                stmt.add(cvar.getAccessAsserts(loc, idc));
                Expression expr = main.typeHandler.convertArith2Boolean(loc,
                        valueType, relr.lrVal.getValue());
                stmt.add(new AssignmentStatement(loc,
                        new LeftHandSide[] { new ArrayLHS(loc, lhs, idc) },
                        new Expression[] { expr }));
            }
        } else {
            for (ResultExpressionListRec child : relr.list) {//TODO revise
                ++indices[pos + 1];
                ResultExpression r;
                if (valueType instanceof StructType) {
                    if (child.list == null) {
                        // handleStructInit expects a nested element on the
                        // first call!
                        ResultExpressionListRec nested = new ResultExpressionListRec();
                        nested.list.add(child);
                        child = nested;
                    }
                    Expression[] idc = new Expression[indices.length];
                    for (int i = 0; i < indices.length; i++)
                        idc[i] = new IntegerLiteral(loc, new InferredType(
                                Type.Integer), indices[i] + SFO.EMPTY);
                    stmt.add(cvar.getAccessAsserts(loc, idc));
                    assert cvar.getValueType() instanceof CStruct;
                    // TODO : could also be a named type, that needs to be
                    // resolved!
                    r = structHandler.handleStructInit(main, memoryHandler, structHandler, this, loc,
                            (StructType) valueType, (CStruct) cvar
                                    .getValueType(),
                            new ArrayLHS(loc, lhs, idc), child,
                            new ArrayList<Integer>(), -1);
                } else {
                    r = handleArrayInit(main, memoryHandler, structHandler, loc, at, cvar,
                            lhs, child, indices, pos + 1);
                }
                decl.addAll(r.decl);
                stmt.addAll(r.stmt);
                auxVars.putAll(r.auxVars);
            }
            indices[pos + 1] = -1;
        }
		assert (main.isAuxVarMapcomplete(decl, auxVars));
        return new ResultExpression(stmt, null, decl, auxVars);
    }

    /**
     * Extracted method to handle IASTSimpleDeclaration holding a
     * ArrayDeclaration.
     * 
     * @param main
     *            the main dispatcher reference.
     * @param structHandler
     *            a reference to the struct handler.
     * @param node
     *            the simple declaration holding the array.
     * @param globalVariables
     *            a reference to the collection holding the variables, that need
     *            to be declared globally in boogie.
     * @param globalVariablesInits
     *            a reference to the collection holding the init statements for
     *            the variables, that need to be declared globally.
     * @return the handled Result.
     */
    public Result handleArrayDeclaration(Dispatcher main, MemoryHandler memoryHandler,  
            StructHandler structHandler, IASTSimpleDeclaration node,
            HashMap<Declaration, CType> globalVariables,
            HashMap<Declaration, ArrayList<Statement>> globalVariablesInits) {
    	return handleArrayDeclaration(main, memoryHandler, structHandler, node,
    			globalVariables, globalVariablesInits, 0);
    }
    
    /**
     * Has additional index.
     * 
	 * @see handleArrayDeclaration()
	 * @param index index of the declaration list
	 */
    public Result handleArrayDeclaration(Dispatcher main, MemoryHandler memoryHandler,
            StructHandler structHandler, IASTSimpleDeclaration node,
            HashMap<Declaration, CType> globalVariables,
            HashMap<Declaration, ArrayList<Statement>> globalVariablesInits,
            int index) {
        CACSLLocation loc = new CACSLLocation(node);
        assert (index >= 0 && index < node.getDeclarators().length);
        IASTDeclarator cDecl = node.getDeclarators()[index];
        assert cDecl instanceof IASTArrayDeclarator;
        IASTArrayDeclarator d = (IASTArrayDeclarator) cDecl;
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
        String cId = d.getName().getRawSignature();
        String bId = main.nameHandler.getUniqueIdentifier(node, cId, //TODO: are all our arrays on the heap or what??
                main.cHandler.getSymbolTable().getCompoundCounter(), false);
        Result res = main.dispatch(node.getDeclSpecifier());
        assert res instanceof ResultSkip || res instanceof ResultTypes;
        if (res instanceof ResultSkip)
            return res;
        if (!(res instanceof ResultTypes)) {
            String msg = "Unexpected Result for Array declaration specifier!";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
        ResultTypes resType = (ResultTypes) res;
        ArrayList<Expression> dimensions = new ArrayList<Expression>();
        if (d.getArrayModifiers() != null) {
            for (IASTArrayModifier m : d.getArrayModifiers()) {
                if (m.getConstantExpression() != null) {
                    Result r = main.dispatch(m.getConstantExpression());
                    assert r instanceof ResultExpression;
                    ResultExpression rex = (ResultExpression) r;
                    assert rex.lrVal != null;
                    stmt.addAll(rex.stmt);
                    decl.addAll(rex.decl);
                    auxVars.putAll(rex.auxVars);
                    if (rex.lrVal.getValue() instanceof IntegerLiteral) {
                        dimensions.add(rex.lrVal.getValue());
                    } else {
                        // use a variable to store the current value!
                        String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYDIM);
                        InferredType tmpType = new InferredType(Type.Integer);
                        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);
                        auxVars.put(tVarDecl, loc);
                        decl.add(tVarDecl);
                        stmt.add(new AssignmentStatement(loc,
                                new LeftHandSide[] { new VariableLHS(loc,
                                        new InferredType(Type.Integer),
                                        tmpName) },
                                new Expression[] { rex.lrVal.getValue() }));
                        dimensions.add(new IdentifierExpression(loc, tmpName));
                    }
                } else {
                    if (dimensions.size() == 0) {
                        // outer most dimension omitted! -> set in init!
                        dimensions.add(null);
                    } else {
                        String msg = "Array modifier may only be omitted for the outer most index!";
                        Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax,
                                msg);
                        throw new IncorrectSyntaxException(msg);
                    }
                }
            }
        }
        ASTType[] dim = new ASTType[dimensions.size()];
        Arrays.fill(dim, new PrimitiveType(loc, SFO.INT));
        ArrayType at = new ArrayType(loc, new InferredType(resType.getType()),
                new String[0], dim, resType.getType());
        // declare the map variable
        VariableDeclaration vdec = new VariableDeclaration(loc,
                new Attribute[0], new VarList[] { new VarList(loc,
                        new String[] { bId }, at) });
        boolean isGlobal = node.getParent() == node.getTranslationUnit();
        if (d.getInitializer() == null) {
            if (dimensions.get(0) == null) {
                String msg = "Array modifier on outer most index may only be omitted, if the array gets initialized!";
                Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
        } else {
            Result initializer = main.dispatch(d.getInitializer());
            assert initializer instanceof ResultExpressionListRec;
            ResultExpressionListRec relr = ((ResultExpressionListRec) initializer);
            if (dimensions.get(0) == null) {
                // set dimension for outer most index!
                dimensions.set(0, new IntegerLiteral(loc, new InferredType(
                        Type.Integer), SFO.EMPTY + relr.list.size()));
            }
            VariableLHS arr = new VariableLHS(loc, new InferredType(
                    resType.getType()), bId);
            int[] idx = new int[dimensions.size()];
            Arrays.fill(idx, -1);
            CArray cvar = new CArray(node.getDeclSpecifier(),
                    dimensions.toArray(new Expression[0]), resType.cvar);
            ResultExpression rex = handleArrayInit(main, memoryHandler, structHandler, loc,
                    at, cvar, arr, relr, idx, -1)
                    .switchToRValue(main, memoryHandler, structHandler, loc);
            if (resType.cvar.isStatic() && !isGlobal) {
                assert rex.decl.isEmpty();
                decl.addAll(rex.decl);
                globalVariablesInits.put(vdec, rex.stmt);
            } else {
                decl.addAll(rex.decl);
                stmt.addAll(rex.stmt);
            }
            auxVars.putAll(rex.auxVars);
        }
        ResultExpression result = new ResultExpression(null, auxVars);
        CArray cvar = new CArray(node.getDeclSpecifier(),
                dimensions.toArray(new Expression[0]), resType.cvar);
        if (main.typeHandler.isStructDeclaration()) {
            // store C variable information into this result, as this is
            // a struct field! We need this information to build the
            // structs C variable information recursively.
            assert resType.cvar != null;
            result.declCTypes.add(cvar);
        }
        if (resType.cvar.isStatic() && !isGlobal) {
            globalVariables.put(vdec, cvar);
        } else {
            decl.add(vdec);
        }
        main.cHandler.getSymbolTable().put(cId,
                new SymbolTableValue(bId, vdec, isGlobal, cvar));
        result.decl.addAll(decl);
        result.stmt.addAll(stmt);
        return result;
    }

    /**
     * Handle a IASTArraySubscriptionExpression.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param node
     *            the node to translate.
     * @return the translation result.
     */
    public Result handleArraySubscriptionExpression(Dispatcher main, MemoryHandler memoryHandler,
    		StructHandler structHandler, IASTArraySubscriptExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
        Stack<Expression> args = new Stack<Expression>();

        IASTExpression arr = node;
        do {
            assert arr instanceof IASTArraySubscriptExpression;
            ResultExpression arg = ((ResultExpression) main
                    .dispatch(((IASTArraySubscriptExpression) arr)
                            .getArgument())).switchToRValue(main, memoryHandler, structHandler, loc);
            args.push(arg.lrVal.getValue());
            stmt.addAll(arg.stmt);
            decl.addAll(arg.decl);
            auxVars.putAll(arg.auxVars);
            arr = ((IASTArraySubscriptExpression) arr).getArrayExpression();
        } while (arr instanceof IASTArraySubscriptExpression);

        ResultExpression rexId = ((ResultExpression) main.dispatch(arr))
        		.switchToRValue(main, memoryHandler, structHandler, loc);
        Expression subExpr = rexId.lrVal.getValue();
        assert rexId.lrVal.cType != null;
        CArray cType = (CArray) rexId.lrVal.cType;

//        Expression expr;
        LeftHandSide lhs = null;
        Expression[] idx = new Expression[args.size()];
        Collections.reverse(args);
        args.toArray(idx);
        if (subExpr instanceof IdentifierExpression) {
//            IdentifierExpression idEx = (IdentifierExpression) subExpr;
        	VariableLHS vlhs = new VariableLHS(loc, subExpr.getType(), 
        			((IdentifierExpression) subExpr).getIdentifier());
            String cId = main.cHandler.getSymbolTable().getCID4BoogieID(
                    vlhs.getIdentifier(), loc);
            stmt.add(cType.getAccessAsserts(loc, idx));
//            expr = new ArrayAccessExpression(loc,
//                    new InferredType(main.cHandler.getSymbolTable()
//                            .getTypeOfVariable(cId, loc)), idEx, idx);
           lhs = new ArrayLHS(loc, 
        		   new InferredType(main.cHandler.getSymbolTable()
        				   .getTypeOfVariable(cId, loc)),
        				   vlhs,
        				   idx);
        } else if (subExpr instanceof StructAccessExpression) {
            StructAccessExpression sae = (StructAccessExpression) subExpr;
            StructLHS slhs = (StructLHS) BoogieASTUtil.getLHSforExpression(sae);
            ASTType t = main.typeHandler.getTypeOfStructLHS(
                    main.cHandler.getSymbolTable(), loc, slhs);
            if (!(t instanceof ArrayType)) {
                String msg = "Type mismatch - cannot take index on a not-array element!";
                Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
            stmt.add(cType.getAccessAsserts(loc, idx));
//            expr = new ArrayAccessExpression(loc, sae.getType(), sae, idx);
            lhs = new ArrayLHS(loc, sae.getType(), slhs, idx);
        } else {
            String msg = "Unexpected result type on left side of array!";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
        return new ResultExpression(stmt, new LocalLValue(lhs, cType.getValueType()), decl, auxVars);
    }

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
		ArrayList<Integer> sizeConstantsAsInt = new ArrayList<Integer>();
//		ArrayList<ASTType> astIndexTypes = new ArrayList<ASTType>();
		Expression overallSize = new IntegerLiteral(loc, new InferredType(Type.Integer), "1");
		Integer overallSizeAsInt = 1;
		for (IASTArrayModifier am : d.getArrayModifiers()) {
			ResultExpression constEx = (ResultExpression) main.
					dispatch(am.getConstantExpression());
			constEx = constEx.switchToRValue(main, //just to be safe..
					memoryHandler, structHandler, loc);
			assert constEx.lrVal instanceof RValue : "we only allow arrays of constant size";
			sizeConstants.add(constEx.lrVal.getValue());
			if (constEx.lrVal.getValue() instanceof IntegerLiteral) {
				Integer constAsInt =  Integer.parseInt(((IntegerLiteral) constEx.lrVal.getValue()).getValue());
				sizeConstantsAsInt.add(constAsInt);
				overallSizeAsInt = overallSizeAsInt * constAsInt;
			} else {
				overallSizeAsInt = 0;
//				assert false : "expecting only int constants for array size";//TODO ..
			}
			
			overallSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
					overallSize, constEx.lrVal.getValue(), loc);//
		}
		
		Expression sizeOfCell = memoryHandler.calculateSizeOf(resType.cvar);
		
		ResultExpression mallocCall = null;
		Expression mallocSize = null;
		if (overallSizeAsInt != 0) {
			mallocSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
					new IntegerLiteral(loc, new InferredType(Type.Integer), overallSizeAsInt.toString()),
					sizeOfCell,
					loc);
		} else {
			mallocSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
					overallSize,
					sizeOfCell,
					loc);
		}
		mallocCall = memoryHandler.getMallocCall(main, functionHandler, 
					mallocSize, loc);	
		
		stmt.addAll(mallocCall.stmt);
		decl.addAll(mallocCall.decl);
		auxVars.putAll(mallocCall.auxVars);
		arrayPointer = mallocCall.lrVal;
		arrayPointer.cType = new CArray(iastDeclSpecifier,  //TODO: think about this type things
				sizeConstants.toArray(new Expression[0]), resType.cvar);
		
		LocalLValue arrayId = new LocalLValue(new VariableLHS(loc, new InferredType(Type.Pointer), bId), arrayPointer.cType);
		Statement assingPtrToArray = new AssignmentStatement(loc, 
				new LeftHandSide[]{ arrayId.getLHS() }, 
				new Expression[]{ arrayPointer.getValue() });
		stmt.add(assingPtrToArray);
		
		//handle initialization
		if (d.getInitializer() != null) {			
//			if (overallSizeAsInt == 0) {
//				assert false : "not yet implemented";
			//not using the ints but making boogie computations right now..
			//however for initialisation we need a size, of course..
			ResultExpressionListRec init = (ResultExpressionListRec) main.dispatch(d.getInitializer());
			ArrayList<Statement> arrayWrites = initArray(memoryHandler, sizeConstantsAsInt, sizeConstants, init.list, 0,
					arrayId.getValue(), sizeOfCell, loc);
			stmt.addAll(arrayWrites);
			
			for (String t : new String[] { SFO.INT, SFO.POINTER,
					SFO.REAL, SFO.BOOL }) {
				functionHandler.getModifiedGlobals()
				.get(functionHandler.getCurrentProcedureID())
				.add(SFO.MEMORY + "_" + t);
			}
		}
		return new ResultExpression(stmt, arrayId, decl, auxVars);
	}
	
//	FIXME: a little inconsistent: here, we assume non-variable, simple sizeConstants while not doing so at arraySubscriptExs
	private ArrayList<Statement> initArray(
			MemoryHandler memoryHandler, ArrayList<Integer> sizeConstantsAsInt,	ArrayList<Expression> sizeConstants, 
			ArrayList<ResultExpressionListRec> list, int depth, Expression startAddress, Expression sizeOfCell,
			ILocation loc) {
		ArrayList<Statement> arrayWrites = new ArrayList<Statement>();
		Integer currentSizeInt = sizeConstantsAsInt.get(depth);
		Expression currentSize = sizeConstants.get(depth);
		
		Expression newStartAddressBase = null;
		Expression newStartAddressOffset = null;
		if (startAddress instanceof StructConstructor) {
			newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
			newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
		}
		
		if (depth == sizeConstantsAsInt.size() - 1) {
			RValue val = null;
			
			for (int i = 0; i < currentSizeInt; i++) {
				if (list.size() > i)
					val = (RValue) list.get(i).lrVal; //if not enough values are given, fill the rest with the last
				
				
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
				for (int j = depth + 1; j < sizeConstants.size(); j++) {
					blockOffset = 
						CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply,
								sizeConstants.get(j),
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
					
				arrayWrites.addAll(
						initArray(memoryHandler, sizeConstantsAsInt, sizeConstants, list.get(i).list, depth + 1,
						MemoryHandler.constructPointerFromBaseAndOffset(
								newStartAddressBase,
								newStartAddressOffsetInner, 
								loc),
						sizeOfCell, loc)); 
			}
		}
		return arrayWrites;
	}

	public Result handleArrayOnHeapSubscriptionExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			IASTArraySubscriptExpression node) {
		ILocation loc = new CACSLLocation(node);
		ResultExpression subScript = (ResultExpression) main.dispatch(node.getArgument());
		ResultExpression array = (ResultExpression) main.dispatch(node.getArrayExpression());
		
		CArray arrayCType = null;
			
		if (node.getArrayExpression() instanceof IASTArraySubscriptExpression) {
			arrayCType = (CArray) array.lrVal.cType;
		} else { // we have reached the innermost subscript
			arrayCType = (CArray) main.cHandler.getSymbolTable().get(
					main.cHandler.getSymbolTable().getCID4BoogieID(
							((IdentifierExpression) array.lrVal.getValue()).getIdentifier(), null), null).getCVariable();
		}
		
		ArrayList<Expression> newDimensions = new ArrayList<Expression>(Arrays.asList(arrayCType.getDimensions()));
			newDimensions.remove(0);//FIXME: first or last??
			CArray outerArrayCType = new CArray(
					arrayCType.getDeclSpec(), newDimensions.toArray(new Expression[0]), arrayCType.getValueType());
			
			Expression offset = subScript.lrVal.getValue();
			offset = computeSubscriptMultiplier(main, memoryHandler, loc,
					arrayCType, offset);	
			
			Expression arrayBase = null;
			Expression arrayOffset = null;
			if (node.getArrayExpression() instanceof IASTArraySubscriptExpression) {
				HeapLValue arrayHlv = (HeapLValue) array.lrVal;
				StructConstructor ptr = (StructConstructor) arrayHlv.getAddress();
				arrayBase = ptr.getFieldValues()[0];
				arrayOffset = ptr.getFieldValues()[1];
			} else{
				Expression arrayAddress = array.lrVal.getValue();
				arrayBase = MemoryHandler.getPointerBaseAddress(arrayAddress, loc);
				arrayOffset = MemoryHandler.getPointerOffset(arrayAddress, loc);
			}
			
			
			offset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus,
					arrayOffset,
					offset, 
					loc);	
			
			Expression newPointer = MemoryHandler
					.constructPointerFromBaseAndOffset(arrayBase, offset, loc);
			
			return new ResultExpression(new HeapLValue(newPointer, outerArrayCType));
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
