/**
 * Class that handles translation of memory related operations.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @date 05.11.2012
 */
public class MemoryHandler {
    /**
     * The "~size" variable identifier.
     */
    private static final String SIZE = "~size";
    /**
     * The "~addr" variable identifier.
     */
    private static final String ADDR = "~addr";
    /**
     * The set holding the Ids of all sizeof constants.
     */
    private HashSet<String> sizeofConsts;
    /**
     * The type describing a pointer.
     */
    public static final ASTType POINTER_TYPE = new NamedType(null,
            new InferredType(Type.Struct), SFO.POINTER, new ASTType[0]);
    /**
     * A set of constants, required for the memory model. E.g. sizeof and offset
     * constants.
     */
    private final HashSet<ConstDeclaration> constants;
    /**
     * A set of axioms, required for the memory model. E.g. for sizeof and
     * offset constants.
     */
    private final HashSet<Axiom> axioms;
    
    /**
     * Add also implementations of malloc, free, write and read functions.
     * TODO: details
     */
	private static final boolean m_AddImplementation = false;

    /**
     * Constructor.
     */
    public MemoryHandler() {
        this.sizeofConsts = new HashSet<String>();
        this.axioms = new HashSet<Axiom>();
        this.constants = new HashSet<ConstDeclaration>();
    }

    /**
     * Declare all variables required for the memory model.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param tuLoc
     *            location to use for declarations.
     * @return a set of declarations.
     */
    public ArrayList<Declaration> declareMemoryModelInfrastructure(
            final Dispatcher main, final ILocation tuLoc) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        if (!main.isMMRequired()) {
            return decl;
        }
        InferredType intIT = new InferredType(Type.Integer);
        InferredType boolIT = new InferredType(Type.Boolean);
        ASTType intType = new PrimitiveType(tuLoc, intIT, SFO.INT);
        ASTType boolType = new PrimitiveType(tuLoc, boolIT, SFO.BOOL);
        // type finite $Pointer$ = { base:int, offset:int };
        VarList fBase = new VarList(tuLoc, new String[] { SFO.POINTER_BASE },
                intType);
        VarList fOffset = new VarList(tuLoc,
                new String[] { SFO.POINTER_OFFSET }, intType);
        VarList[] fields = new VarList[] { fBase, fOffset };
        ASTType pointerType = new StructType(tuLoc, new InferredType(
                Type.Struct), fields);
        decl.add(new TypeDeclaration(tuLoc, new Attribute[0], true,
                SFO.POINTER, new String[0], pointerType));
        // NULL Pointer
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { new VarList(tuLoc, new String[] { SFO.NULL },
                        pointerType) }));
        // to add a type declaration for "real"
        // decl.add(new TypeDeclaration(tuLoc, new Attribute[0], false,
        // SFO.REAL, new String[0]));
        decl.addAll(declareMemoryArrays(tuLoc, main));
        // var #valid : [int]bool;
        ASTType validType = new ArrayType(tuLoc, new String[0],
                new ASTType[] { intType }, boolType);
        VarList vlV = new VarList(tuLoc, new String[] { SFO.VALID }, validType);
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { vlV }));
        // var #length : [int]int;
        ASTType lengthType = new ArrayType(tuLoc, new String[0],
                new ASTType[] { intType }, intType);
        VarList vlL = new VarList(tuLoc, new String[] { SFO.LENGTH },
                lengthType);
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { vlL }));
        decl.addAll(declareFree(tuLoc));
        decl.addAll(declareMalloc(tuLoc));
        decl.addAll(constants);
        decl.addAll(axioms);
        return decl;
    }

    /**
     * Declare sizeof constants and add to the sizeOfConst set.
     * 
     * @param l
     *            the location.
     * @param t
     *            the type string.
     */
    private void declareSizeOf(ILocation l, String t) {
        String id = SFO.SIZEOF + t;
        if (sizeofConsts.contains(id)) {
            return;
        }
        InferredType intIT = new InferredType(Type.Integer);
        ASTType intType = new PrimitiveType(l, intIT, SFO.INT);
        // const #sizeof~t : int;
        constants.add(new ConstDeclaration(l, new Attribute[0], false,
                new VarList(l, new String[] { id }, intType), null, false));
        Expression idex = new IdentifierExpression(l, id);
        // axiom #sizeof~t > 0;
        axioms.add(new Axiom(l, new Attribute[0], new BinaryExpression(l,
                Operator.COMPGT, idex, new IntegerLiteral(l, SFO.NR0))));
        sizeofConsts.add(id);
    }

    /**
     * Declares the memory arrays <code>#memory_int</code>,
     * <code>#memory_bool</code>, <code>#memory_real</code> and
     * <code>#memory_$Pointer$</code>, as well as read and write procedures for
     * these arrays.
     * 
     * @param l
     *            the location of the translation unit.
     * @param main 
     * @return the declarations for the memory arrays <code>#memory_int</code>,
     *         <code>#memory_bool</code>, <code>#memory_real</code> and
     *         <code>#memory_$Pointer$</code>, as well as read and write
     *         procedures for these arrays.
     */
    private ArrayList<Declaration> declareMemoryArrays(final ILocation l, Dispatcher main) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        InferredType intIT = new InferredType(Type.Integer);
        InferredType boolIT = new InferredType(Type.Boolean);
        InferredType realIT = new InferredType(Type.Real);
        ASTType intType = new PrimitiveType(l, intIT, SFO.INT);
        ASTType boolType = new PrimitiveType(l, boolIT, SFO.BOOL);
        ASTType realType = new PrimitiveType(l, realIT, SFO.REAL);
        // add memory arrays and access procedures
        String[] tName = new String[] { SFO.POINTER, SFO.INT, SFO.BOOL,
                SFO.REAL };
        ASTType[] ts = new ASTType[] { POINTER_TYPE, intType, boolType,
                realType };
        assert tName.length == ts.length;
        for (int i = 0; i < tName.length; i++) {
            declareSizeOf(l, tName[i]);
            // var #memory_tName[i] : [$Pointer$]ts[i];
            ASTType memoryType = new ArrayType(l, new String[0],
                    new ASTType[] { POINTER_TYPE }, ts[i]);
            VarList vlM = new VarList(l, new String[] { SFO.MEMORY + "_"
                    + tName[i] }, memoryType);
            decl.add(new VariableDeclaration(l, new Attribute[0],
                    new VarList[] { vlM }));
            // create and add read and write procedure
            String value = "#value";
            String inPtr = "#ptr";
            Expression idVal = new IdentifierExpression(l, value);
            Expression idPtr = new IdentifierExpression(l, inPtr);
            Expression[] idc = new Expression[] { idPtr };
            String nwrite = "write~" + tName[i];
            String nread = "read~" + tName[i];
            VarList[] inWrite = new VarList[] {
                    new VarList(l, new String[] { value }, ts[i]),
                    new VarList(l, new String[] { inPtr }, POINTER_TYPE) };
            Expression valid = new IdentifierExpression(l, SFO.VALID);
            Expression addr = new IdentifierExpression(l, inPtr);
            Expression addrBase = new StructAccessExpression(l, intIT, addr,
                    SFO.POINTER_BASE);
            Expression[] idcWrite = new Expression[] { addrBase };
            String[] modified = new String[tName.length];
            for (int j = 0; j < modified.length; j++) {
                modified[j] = SFO.MEMORY + "_" + tName[j];
            }
            Specification[] swrite = new Specification[3 + modified.length];
            int sidx = 0;
            // requires #valid[#ptr!base];
            swrite[sidx++] = new RequiresSpecification(l, false,
                    new ArrayAccessExpression(l, boolIT, valid, idcWrite));
            // modifies #memory_int, #memory_bool, #memory_$Pointer$,
            // #memory_real;
            swrite[sidx++] = new ModifiesSpecification(l, false, modified);
            // requires #sizeof~$Pointer$ + #ptr!offset <= #length[#ptr!base];
            Expression ptrOff = new StructAccessExpression(l, intIT, idPtr,
                    SFO.POINTER_OFFSET);
            Expression ptrBase = new StructAccessExpression(l, intIT, idPtr,
                    SFO.POINTER_BASE);
            Expression length = new ArrayAccessExpression(l,
                    new IdentifierExpression(l, SFO.LENGTH),
                    new Expression[] { ptrBase });
            swrite[sidx++] = new RequiresSpecification(l, false,
                    new BinaryExpression(l, Operator.COMPLEQ,
                            new BinaryExpression(l, Operator.ARITHPLUS,
                                    new IdentifierExpression(l, SFO.SIZEOF
                                            + tName[i]), ptrOff), length));
            for (int j = 0; j < modified.length; j++) {
                // ensures #memory_int == old(#valid)[~addr!base := false];
                Expression memA = new IdentifierExpression(l, SFO.MEMORY + "_"
                        + tName[j]);
                if (i == j) {
                    swrite[sidx++] = new EnsuresSpecification(
                            l,
                            false,
                            new BinaryExpression(
                                    l,
                                    Operator.COMPEQ,
                                    memA,
                                    new ArrayStoreExpression(
                                            l,
                                            new UnaryExpression(
                                                    l,
                                                    UnaryExpression.Operator.OLD,
                                                    memA), idc, idVal)));
                } else {
                    Expression aae = new ArrayAccessExpression(l, memA, idc);
                    swrite[sidx++] = new EnsuresSpecification(
                            l,
                            false,
                            new BinaryExpression(
                                    l,
                                    Operator.COMPEQ,
                                    memA,
                                    new ArrayStoreExpression(
                                            l,
                                            new UnaryExpression(
                                                    l,
                                                    UnaryExpression.Operator.OLD,
                                                    memA), idc, aae)));
                }
            }
            decl.add(new Procedure(l, new Attribute[0], nwrite, new String[0],
                    inWrite, new VarList[0], swrite, null));
            if (m_AddImplementation) {
            	VariableDeclaration[] writeDecl = new VariableDeclaration[ts.length];
            	Statement[] writeBlock = new Statement[2 * ts.length - 1];
            	for (int j = 0, k = 0; j < ts.length; j++, k++) {
            		String tmpVar = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);	
            		writeDecl[j] = new VariableDeclaration(l, new Attribute[0],
            				new VarList[] { new VarList(l, new String[] { tmpVar },
            						ts[j]) });
            		VariableLHS arr = new VariableLHS(l, SFO.MEMORY + "_"
            				+ tName[j]);
            		LeftHandSide[] arrL = new LeftHandSide[] { new ArrayLHS(l, arr,
            				idc) };
            		if (i == j) {
            			writeBlock[k] = new AssignmentStatement(l, arrL,
            					new Expression[] { idVal });
            		} else {
            			writeBlock[k] = new HavocStatement(l,
            					new String[] { tmpVar });
            			writeBlock[++k] = new AssignmentStatement(l, arrL,
            					new Expression[] { new IdentifierExpression(l,
            							tmpVar) });
            		}
            	}
            	Body bwrite = new Body(l, writeDecl, writeBlock);
            	decl.add(new Procedure(l, new Attribute[0], nwrite, new String[0],
            			inWrite, new VarList[0], null, bwrite));
            }
            VarList[] inRead = new VarList[] { new VarList(l,
                    new String[] { inPtr }, POINTER_TYPE) };
            VarList[] outRead = new VarList[] { new VarList(l,
                    new String[] { value }, ts[i]) };
            Specification[] sread = new Specification[] {
                    // requires #valid[#ptr!base];
                    new RequiresSpecification(l, false,
                            new ArrayAccessExpression(l, boolIT, valid,
                                    idcWrite)),
                    // requires #sizeof~$Pointer$ + #ptr!offset <=
                    // #length[#ptr!base];
                    new RequiresSpecification(l, false, new BinaryExpression(l,
                            Operator.COMPLEQ, new BinaryExpression(l,
                                    Operator.ARITHPLUS,
                                    new IdentifierExpression(l, SFO.SIZEOF
                                            + tName[i]), ptrOff), length)) };
            decl.add(new Procedure(l, new Attribute[0], nread, new String[0],
                    inRead, outRead, sread, null));
            if (m_AddImplementation) {
            	Expression arr = new IdentifierExpression(l, SFO.MEMORY + "_"
            			+ tName[i]);
            	Expression arrE = new ArrayAccessExpression(l, arr, idc);
            	Statement[] readBlock = new Statement[] { new AssignmentStatement(
            			l, new LeftHandSide[] { new VariableLHS(l, value) },
            			new Expression[] { arrE }) };
            	Body bread = new Body(l, new VariableDeclaration[0], readBlock);
            	decl.add(new Procedure(l, new Attribute[0], nread, new String[0],
            			inRead, outRead, null, bread));
            }
        }
        return decl;
    }

    /**
     * Generate <code>procedure ~free(~addr:$Pointer$) returns()</code>'s
     * declaration and implementation.
     * 
     * @param tuLoc
     *            the location for the new nodes.
     * @return declaration and implementation of procedure <code>~free</code>
     */
    private static ArrayList<Declaration> declareFree(final ILocation tuLoc) {
        InferredType intIT = new InferredType(Type.Integer);
        InferredType boolIT = new InferredType(Type.Boolean);
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        // procedure ~free(~addr:$Pointer$) returns();
        // requires ~addr!offset = 0;
        // requires #valid[~addr!base];
        // ensures #valid = old(valid)[~addr!base := false];
        // modifies #valid;
        Expression nr0 = new IntegerLiteral(tuLoc, SFO.NR0);
        Expression bLFalse = new BooleanLiteral(tuLoc, boolIT, false);
        Expression addr = new IdentifierExpression(tuLoc, ADDR);
        Expression valid = new IdentifierExpression(tuLoc, SFO.VALID);
        Expression addrOffset = new StructAccessExpression(tuLoc, intIT, addr,
                SFO.POINTER_OFFSET);
        Expression addrBase = new StructAccessExpression(tuLoc, intIT, addr,
                SFO.POINTER_BASE);
        Expression[] idcFree = new Expression[] { addrBase };
        Specification[] specFree = new Specification[] {
                new RequiresSpecification(tuLoc, false, new BinaryExpression(
                        tuLoc, Operator.COMPEQ, addrOffset, nr0)),
                new RequiresSpecification(
                        tuLoc,
                        false,
                        new ArrayAccessExpression(tuLoc, boolIT, valid, idcFree)),
                new EnsuresSpecification(tuLoc, false, new BinaryExpression(
                        tuLoc, Operator.COMPEQ, valid,
                        new ArrayStoreExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcFree, bLFalse))),
                new ModifiesSpecification(tuLoc, false,
                        new String[] { SFO.VALID }) };
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.FREE,
                new String[0], new VarList[] { new VarList(tuLoc,
                        new String[] { ADDR }, POINTER_TYPE) }, new VarList[0],
                specFree, null));
        if (m_AddImplementation) {
        	// procedure ~free(~addr:$Pointer$) returns() {
        	// #valid[~addr!base] := false;
        	// // havoc #memory[n];
        	// }
        	LeftHandSide[] lhs = new LeftHandSide[] { new ArrayLHS(tuLoc,
        			new VariableLHS(tuLoc, SFO.VALID), idcFree) };
        	Expression[] rhsFree = new Expression[] { bLFalse };
        	Body bodyFree = new Body(
        			tuLoc,
        			new VariableDeclaration[0],
        			new Statement[] { new AssignmentStatement(tuLoc, lhs, rhsFree) });
        	decl.add(new Procedure(tuLoc, new Attribute[0], SFO.FREE,
        			new String[0], new VarList[] { new VarList(tuLoc,
        					new String[] { ADDR }, POINTER_TYPE) }, new VarList[0],
        					null, bodyFree));
        }
        return decl;
    }

    /**
     * Generate
     * <code>procedure ~malloc(~size:int) returns (#res:$Pointer$);</code>'s
     * declaration and implementation.
     * 
     * @param tuLoc
     *            the location for the new nodes.
     * @return declaration and implementation of procedure <code>~malloc</code>
     */
    private static ArrayList<Declaration> declareMalloc(final ILocation tuLoc) {
        InferredType pointerIT = new InferredType(Type.Pointer);
        InferredType intIT = new InferredType(Type.Integer);
        InferredType boolIT = new InferredType(Type.Boolean);
        ASTType intType = new PrimitiveType(tuLoc, intIT, SFO.INT);
        Expression nr0 = new IntegerLiteral(tuLoc, SFO.NR0);
        Expression bLFalse = new BooleanLiteral(tuLoc, boolIT, false);
        Expression addr = new IdentifierExpression(tuLoc, ADDR);
        Expression valid = new IdentifierExpression(tuLoc, SFO.VALID);
        Expression addrOffset = new StructAccessExpression(tuLoc, intIT, addr,
                SFO.POINTER_OFFSET);
        Expression addrBase = new StructAccessExpression(tuLoc, intIT, addr,
                SFO.POINTER_BASE);
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        // procedure ~malloc(~size:int) returns (#res:$Pointer$);
        // requires ~size >= 0;
        // ensures old(#valid)[#res!base] = false;
        // ensures #valid = old(#valid)[#res!base := true];
        // ensures #res!offset == 0;
        // ensures #res!base != 0;
        // ensures #length = old(#length)[#res!base := ~size];
        // modifies #length, #valid;
        Expression res = new IdentifierExpression(tuLoc, pointerIT, SFO.RES);
        Expression length = new IdentifierExpression(tuLoc, SFO.LENGTH);
        Expression[] idcMalloc = new Expression[] { new StructAccessExpression(
                tuLoc, intIT, res, SFO.POINTER_BASE) };
        Expression bLTrue = new BooleanLiteral(tuLoc, boolIT, true);
        IdentifierExpression size = new IdentifierExpression(tuLoc, intIT, SIZE);
        Specification[] specMalloc = new Specification[7];
        specMalloc[0] = new RequiresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPGEQ, size, nr0));
        specMalloc[1] = new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ,
                        new ArrayAccessExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc), bLFalse));
        specMalloc[2] = new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ, valid,
                        new ArrayStoreExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc, bLTrue)));
        specMalloc[3] = new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ,
                        new StructAccessExpression(tuLoc, intIT, res,
                                SFO.POINTER_OFFSET), nr0));
        specMalloc[4] = new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPNEQ,
                        new StructAccessExpression(tuLoc, intIT, res,
                                SFO.POINTER_BASE), nr0));
        specMalloc[5] = new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ, length,
                        new ArrayStoreExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, length),
                                idcMalloc, size)));
        specMalloc[6] = new ModifiesSpecification(tuLoc, false, new String[] {
                SFO.VALID, SFO.LENGTH });
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.MALLOC,
                new String[0], new VarList[] { new VarList(tuLoc,
                        new String[] { SIZE }, intType) },
                new VarList[] { new VarList(tuLoc, new String[] { SFO.RES },
                        POINTER_TYPE) }, specMalloc, null));
        if (m_AddImplementation) {
        	// procedure ~malloc(~size:int) returns (#res:pointer) {
        	// var ~addr : pointer;
        	//
        	// assume ~addr!offset = 0;
        	// assume ~addr!base != 0;
        	// assume !#valid[~addr!base];
        	// // #valid setzen
        	// #valid = #valid[~addr!base := true];
        	// #length = #length[~addr!base := size];
        	// // return pointer
        	// #res := ~addr;
        	// }
        	Expression[] idcAddrBase = new Expression[] { addrBase };
        	VariableDeclaration[] localVars = new VariableDeclaration[] { new VariableDeclaration(
        			tuLoc, new Attribute[0], new VarList[] { new VarList(tuLoc,
        					new String[] { ADDR }, POINTER_TYPE) }) };
        	Statement[] block = new Statement[6];
        	block[0] = new AssumeStatement(tuLoc, new BinaryExpression(tuLoc,
        			Operator.COMPEQ, addrOffset, nr0));
        	block[1] = new AssumeStatement(tuLoc, new BinaryExpression(tuLoc,
        			Operator.COMPNEQ, addrBase, nr0));
        	block[2] = new AssumeStatement(tuLoc, new UnaryExpression(tuLoc,
        			UnaryExpression.Operator.LOGICNEG, new ArrayAccessExpression(
        					tuLoc, valid, idcAddrBase)));
        	block[3] = new AssignmentStatement(tuLoc,
        			new LeftHandSide[] { new VariableLHS(tuLoc, SFO.VALID) },
        			new Expression[] { new ArrayStoreExpression(tuLoc, valid,
        					idcAddrBase, bLTrue) });
        	block[4] = new AssignmentStatement(tuLoc,
        			new LeftHandSide[] { new VariableLHS(tuLoc, SFO.LENGTH) },
        			new Expression[] { new ArrayStoreExpression(tuLoc, length,
        					idcAddrBase, size) });
        	block[5] = new AssignmentStatement(
        			tuLoc,
        			new LeftHandSide[] { new VariableLHS(tuLoc, pointerIT, SFO.RES) },
        			new Expression[] { addr });
        	Body bodyMalloc = new Body(tuLoc, localVars, block);
        	decl.add(new Procedure(tuLoc, new Attribute[0], SFO.MALLOC,
        			new String[0], new VarList[] { new VarList(tuLoc,
        					new String[] { SIZE }, intType) },
        					new VarList[] { new VarList(tuLoc, new String[] { SFO.RES },
        							POINTER_TYPE) }, null, bodyMalloc));
        }
        return decl;
    }

    /**
     * Creates a function call expression for the ~free(e) function!
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param fh
     *            a reference to the FunctionHandler - required to add
     *            informations to the call graph.
     * @param e
     *            the expression referring to the pointer, that should be
     *            free'd.
     * @param loc
     *            Location for errors and new nodes in the AST.
     * @return a function call expression for ~free(e).
     */
    public ResultExpression getFreeCall(Dispatcher main, FunctionHandler fh,
            Expression e, ILocation loc) {
        String bId = BoogieASTUtil.getLeftMostId(e);
        if (!main.cHandler.getSymbolTable().containsBoogieSymbol(bId)) {
            String msg = "Cannot free variable " + bId
                    + " as it is not in the current scope!";
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        String cId = main.cHandler.getSymbolTable().getCID4BoogieID(bId, loc);
        CType cvar = main.cHandler.getSymbolTable().get(cId, loc)
                .getCVariable();
        if (!(cvar instanceof CPointer)) {
            String msg = "Cannot free the non pointer variable " + cId;
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        // Further checks are done in the precondition of ~free()!
        // ~free(E);
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        stmt.add(new CallStatement(loc, false, new String[0], SFO.FREE,
                new Expression[] { e }));
        // add required information to function handler.
        if (fh.getCurrentProcedureID() != null) {
            HashSet<String> mgM = new HashSet<String>();
            mgM.add(SFO.VALID);
            if (!fh.getModifiedGlobals().containsKey(SFO.FREE)) {
                fh.getModifiedGlobals().put(SFO.FREE, mgM);
                fh.getCallGraph().put(SFO.FREE, new HashSet<String>());
            }
            fh.getCallGraph().get(fh.getCurrentProcedureID()).add(SFO.FREE);
        }
		Map<VariableDeclaration, CACSLLocation> emptyAuxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>(0);
		assert (main.isAuxVarMapcomplete(decl, emptyAuxVars));
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }

    /**
     * Creates a function call expression for the ~malloc(size) function!
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param fh
     *            a reference to the FunctionHandler - required to add
     *            informations to the call graph.
     * @param size
     *            the expression referring to size of the memory to be
     *            allocated.
     * @param loc
     *            Location for errors and new nodes in the AST.
     * @return a function call expression for ~malloc(size).
     */
    public ResultExpression getMallocCall(Dispatcher main, FunctionHandler fh,
            Expression size, CACSLLocation loc) {
        if (!(size.getType() instanceof InferredType)
                || ((InferredType) size.getType()).getType() != Type.Integer) {
            String msg = "Invalid parameter for " + SFO.MALLOC;
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        // Further checks are done in the precondition of ~malloc()!
        // ~malloc(SIZE);
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
        InferredType it = new InferredType(Type.Pointer);
        Expression[] args = new Expression[] { size };
        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MALLOC);
        InferredType tmpIType = new InferredType(Type.Pointer);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, tmpIType, loc);
        auxVars.put(tVarDecl, loc);
        decl.add(tVarDecl);
        stmt.add(new CallStatement(loc, false, new String[] { tmpId },
                SFO.MALLOC, args));
        Expression e = new IdentifierExpression(loc, it, tmpId);
        // add required information to function handler.
        if (fh.getCurrentProcedureID() != null) {
            HashSet<String> mgM = new HashSet<String>();
            mgM.add(SFO.VALID);
            mgM.add(SFO.LENGTH);
            if (!fh.getModifiedGlobals().containsKey(SFO.MALLOC)) {
                fh.getModifiedGlobals().put(SFO.MALLOC, mgM);
                fh.getCallGraph().put(SFO.MALLOC, new HashSet<String>());
            }
            fh.getCallGraph().get(fh.getCurrentProcedureID()).add(SFO.MALLOC);
        }
		assert (main.isAuxVarMapcomplete(decl, auxVars));
        return new ResultExpression(stmt, e, decl, auxVars);
    }

    /**
     * Calculate constants and their dependencies.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param declSpec
     *            the declaration specifier to work on.
     * @return an idExpression to the constant describing this typeIds size
     */
    public Expression getSizeOf(Dispatcher main, IASTDeclSpecifier declSpec) {
        ILocation loc = new CACSLLocation(declSpec);
        InferredType intIt = new InferredType(Type.Integer);
        ResultTypes rt = (ResultTypes) main.dispatch(declSpec);
        String constId = getSizeOfId(rt.cvar);
        return new IdentifierExpression(loc, intIt, constId);
    }

    /**
     * Calculate constants and their dependencies.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param ex
     *            the expression to work on.
     * @return an idExpression to the constant describing this typeIds size
     */
    public Expression getSizeOf(Dispatcher main, IASTExpression ex) {
        ResultExpression rex = (ResultExpression) main.dispatch(ex);
        Expression e = rex.expr;
        ILocation loc = e.getLocation();
        if (e instanceof IdentifierExpression
                || e instanceof StructAccessExpression
                || e instanceof ArrayAccessExpression) {
            String bId = BoogieASTUtil.getLeftMostId(e);
            String cId = main.cHandler.getSymbolTable().getCID4BoogieID(bId,
                    loc);
            CType cvar = main.cHandler.getSymbolTable().get(cId, loc)
                    .getCVariable();
            cvar = cvar.getCVarForAccessExpression(e);
            InferredType intIt = new InferredType(Type.Integer);
            String constId = SFO.SIZEOF + cvar.toString();
            return new IdentifierExpression(loc, intIt, constId);
        }
        if (ex instanceof IASTLiteralExpression) {
            // TODO
            // IASTLiteralExpression ile = ((IASTLiteralExpression) ex);
            // switch (ile.getKind()) {
            // case IASTLiteralExpression.lk_float_constant:
            //
            // case IASTLiteralExpression.lk_char_constant:
            //
            // case IASTLiteralExpression.lk_integer_constant:
            //
            // case IASTLiteralExpression.lk_string_literal:
            //
            // case IASTLiteralExpression.lk_false:
            //
            // case IASTLiteralExpression.lk_true:
            //
            // default:
            String msg = "Unknown or unsupported kind of IASTLiteralExpression";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
            // }
        }
        String msg = "Unexpected expression in sizeof()";
        Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
        throw new IncorrectSyntaxException(msg);
    }

    /**
     * Calculate the sizeof constants for the given CType.
     * 
     * @param cvar
     *            the CVariable to work on.
     * @return a reference to the constant, holding sizeof cvar.
     */
    public IdentifierExpression calculateSizeOf(CType cvar) {
        assert cvar != null;
        ILocation loc = cvar.getCASTLocation();
        ASTType intT = new PrimitiveType(loc, SFO.INT);
        String id = getSizeOfId(cvar);
        IdentifierExpression idex = new IdentifierExpression(loc, id);
        Attribute[] attr = new Attribute[0];
        if (!sizeofConsts.contains(id)) {
            this.constants.add(new ConstDeclaration(loc, attr, false,
                    new VarList(loc, new String[] { id }, intT), null, false));
            this.axioms.add(new Axiom(loc, attr, new BinaryExpression(loc,
                    Operator.COMPGT, idex, new IntegerLiteral(loc, SFO.NR0))));
            sizeofConsts.add(id);
            if (cvar instanceof CArray) {
                CArray ca = (CArray) cvar;
                Expression valSize = calculateSizeOf(ca.getValueType());
                Expression nrElem = new IntegerLiteral(loc, SFO.EMPTY
                        + ca.getDimensions().length);
                Expression size = new BinaryExpression(loc, Operator.ARITHMUL,
                        nrElem, valSize);
                Expression f = new BinaryExpression(loc, Operator.COMPEQ, idex,
                        size);
                this.axioms.add(new Axiom(loc, attr, f));
            } else if (cvar instanceof CStruct) {
                CStruct cs = (CStruct) cvar;
                Expression nextOffset = new IntegerLiteral(loc, SFO.NR0);
                for (int i = 0; i < cs.getFieldCount(); i++) {
                    CType csf = cs.getFieldTypes()[i];
                    String csfId = cs.getFieldIds()[i];
                    String oId = SFO.OFFSET + cvar.toString() + "~" + csfId;
                    this.constants.add(new ConstDeclaration(loc, attr, false,
                            new VarList(loc, new String[] { oId }, intT), null,
                            false));
                    Expression offIdEx = new IdentifierExpression(loc, oId);
                    Expression f = new BinaryExpression(loc, Operator.COMPEQ,
                            offIdEx, nextOffset);
                    this.axioms.add(new Axiom(loc, attr, f));
                    Expression fieldSize = calculateSizeOf(csf);
                    nextOffset = new BinaryExpression(loc, Operator.ARITHPLUS,
                            nextOffset, fieldSize);
                }
                // add an axiom : sizeof cvar (>)= nextOffset
                Expression f = new BinaryExpression(loc, Operator.COMPGEQ,
                        idex, nextOffset);
                this.axioms.add(new Axiom(loc, attr, f));
            } else if (cvar instanceof CNamed) {
                // add an axiom, binding the sizeof of the named type to
                // the sizeof of the underlying type
                CNamed cn = ((CNamed) cvar);
                Expression e = calculateSizeOf(cn.getUnderlyingType());
                Expression f = new BinaryExpression(loc, Operator.COMPEQ, idex,
                        e);
                this.axioms.add(new Axiom(loc, attr, f));
                // NB: I'm not sure, if this is really required! I think we
                // resolve all named types during translation anyway ... and the
                // constants accordingly ...
            } else if (cvar instanceof CEnum) {
                // Here we return a new constant, which might (!) be
                // different from all others (i.e. not the same as int!)
                // the size of these variables is not bound to any value, except
                // it is specified, that it must be capable of holding the max.
                // value of the corresponding possible enums value domain!
                // TODO : no idea how to do that, w/o log_2 function in boogie!
                // so it is just ignored and assumed to be >0!
            }
        }
        return idex;
    }
    
    /**
     * Given a CType return the identifier of the corresponding sizeOf constant.
     */
    private String getSizeOfId(CType cvar) {
    	String result;
    	if (cvar.toString().equals("INT")) {
    		result = SFO.SIZEOF + SFO.INT;
    	} else {
    		throw new UnsupportedOperationException("not yet implemented");
    	}
    	return result;
    }

    /**
     * Checks, if an accessed pointer points to a valid location in memory.
     * 
     * @param idx
     *            the pointer to check.
     * @return an assert statement that checks, whether the accessed memory
     *         location is valid.
     */
    public Statement checkValidityOfAccess(Expression idx) {
        assert idx.getType() instanceof InferredType
                && ((InferredType) idx.getType()).getType() == Type.Pointer;
        // assert #valid[idx!base];
        ILocation loc = idx.getLocation();
        Expression array = new IdentifierExpression(loc, SFO.VALID);
        Expression idxBase = new StructAccessExpression(loc, idx,
                SFO.POINTER_BASE);
        Expression formula = new ArrayAccessExpression(loc, array,
                new Expression[] { idxBase });
        assert loc instanceof CACSLLocation;
        CACSLLocation assertLoc = new CACSLLocation((CACSLLocation) loc,
                new Check(Check.Spec.INVALID_MEMORY_ACCESS));
        return new AssertStatement(assertLoc, formula);
    }

    /**
     * Generates a call of the read procedure and writes the returned value to a
     * temp variable, returned in the expression of the returned
     * ResultExpression.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param it
     *            the type to read.
     * @param tPointer
     *            the address to read from.
     * @return all declarations and statements required to perform the read,
     *         plus an identifierExpression holding the read value.
     */
    public ResultExpression getReadCall(final Dispatcher main,
            final InferredType it, final Expression tPointer) {
        assert tPointer.getType() instanceof InferredType
                && ((InferredType) tPointer.getType()).getType() == Type.Pointer;
        // assert #valid[tPointer!base];
        // tmp = "read_$Pointer$(tPointer);"
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
        CACSLLocation loc = (CACSLLocation) tPointer.getLocation();
        String t = SFO.EMPTY;
        switch (it.getType()) {
            case Boolean:
                t = SFO.BOOL;
                break;
            case Integer:
                t = SFO.INT;
                break;
            case Pointer:
                t = SFO.POINTER;
                break;
            case Real:
                t = SFO.REAL;
                break;
            case String:
            case Struct:
            case Unknown:
            case Void:
            default:
                String m = "Can't read the given type!";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, m);
                throw new UnsupportedSyntaxException(m);
        }
        assert t != SFO.EMPTY;
        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, it, loc);
        auxVars.put(tVarDecl, loc);
        decl.add(tVarDecl);
        String[] lhs = new String[] { tmpId };
        stmt.add(new CallStatement(loc, false, lhs, "read~" + t,
                new Expression[] { tPointer }));
		assert (main.isAuxVarMapcomplete(decl, auxVars));
        return new ResultExpression(stmt, new IdentifierExpression(loc, it,
                tmpId), decl, auxVars);
    }

    /**
     * Generates a procedure call to writeT(val, ptr), writing val to the
     * according memory array.
     * 
     * @param tPointer
     *            the location to write to.
     * @param val
     *            the value to write.
     * @return the required Statements to perform the write.
     */
    public ResultExpression getWriteCall(final Expression tPointer,
            final Expression val) {
        assert tPointer.getType() instanceof InferredType
                && ((InferredType) tPointer.getType()).getType() == Type.Pointer;
        assert val.getType() instanceof InferredType;
        ILocation loc = tPointer.getLocation();
        InferredType it = (InferredType) val.getType();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        String t = SFO.EMPTY;
        switch (it.getType()) {
            case Boolean:
                t = SFO.BOOL;
                break;
            case Integer:
                t = SFO.INT;
                break;
            case Pointer:
                t = SFO.POINTER;
                break;
            case Real:
                t = SFO.REAL;
                break;
            case String:
            case Struct:
            case Unknown:
            case Void:
            default:
                String m = "Can't read the given type!";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, m);
                throw new UnsupportedSyntaxException(m);
        }
        assert t != SFO.EMPTY;

        String[] lhs = new String[] {};
        stmt.add(new CallStatement(loc, false, lhs, "write~" + t,
                new Expression[] { val, tPointer }));
		Map<VariableDeclaration, CACSLLocation> emptyAuxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>(0);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }

    /**
     * Handles manipulations of pointer variables.
     * 
     * @param ptr
     *            the pointer to work on.
     * @param op
     *            the operator to be used.
     * @param val
     *            the value to be used.
     * @return an assignment of form
     *         <code>ptr.offset := ptr.offset op val;</code>.
     */
    public ResultExpression manipulatePointer(Expression ptr,
            BinaryExpression.Operator op, Expression val) {
        assert ptr.getType() instanceof InferredType;
        assert ((InferredType) ptr.getType()).getType() == Type.Pointer;
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        ILocation loc = ptr.getLocation();
        Expression ptrOffset = new StructAccessExpression(loc, ptr,
                SFO.POINTER_OFFSET);
        stmt.add(new AssignmentStatement(loc,
                new LeftHandSide[] { BoogieASTUtil
                        .getLHSforExpression(ptrOffset) },
                new Expression[] { new BinaryExpression(ptr.getLocation(),
                        new InferredType(Type.Integer), op, ptrOffset, val) }));
        // NOTE: the following checks are too strict! The variable can be
        // out of bounds, iff there is no memory access with this pointer!
        // Expression ptrBase = new StructAccessExpression(loc, ptr,
        // SFO.POINTER_BASE);
        // Expression length = new ArrayAccessExpression(loc,
        // new IdentifierExpression(loc, SFO.LENGTH),
        // new Expression[] { ptrBase });
        // stmt.add(new AssertStatement(loc, new BinaryExpression(loc,
        // BinaryExpression.Operator.COMPLEQ, ptrOffset, length)));
        // stmt.add(new AssertStatement(loc, new BinaryExpression(loc,
        // Operator.COMPGEQ, ptrOffset, new IntegerLiteral(loc, SFO.NR0))));
		Map<VariableDeclaration, CACSLLocation> emptyAuxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>(0);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }
}
