/**
 * Class that handles translation of memory related operations.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer.POINTER_ALLOCATED;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer.POINTER_BASE_VALIDITY;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;
import de.uni_freiburg.informatik.ultimate.util.LinkedScopedHashMap;

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
    private LinkedHashSet<String> sizeofConsts;
    /**
     * The type describing a pointer.
     */
    public static final ASTType POINTER_TYPE = new NamedType(null,
            new InferredType(Type.Struct), SFO.POINTER, new ASTType[0]);
    /**
     * A set of constants, required for the memory model. E.g. sizeof and offset
     * constants.
     */
    private final LinkedHashSet<ConstDeclaration> constants;
    /**
     * A set of axioms, required for the memory model. E.g. for sizeof and
     * offset constants.
     */
    private final LinkedHashSet<Axiom> axioms;
    
    /**
     * Add also implementations of malloc, free, write and read functions.
     * TODO: details
     */
	private static final boolean m_AddImplementation = false;
	
	
	private final POINTER_BASE_VALIDITY m_PointerBaseValidity;
	private final POINTER_ALLOCATED m_PointerAllocated;
	private final boolean m_CheckFreeValid;
	private final boolean m_CheckMallocNonNegative;
	
	//needed for adding modifies clauses
	private FunctionHandler m_functionHandler;

	/**
	 * This set contains those pointers that we have to malloc at the beginning
	 * and free at the end of the current scope;
	 */
	LinkedScopedHashMap<LocalLValue, Integer> mallocedAuxPointers;

    /**
     * Constructor.
     * @param checkPointerValidity 
     */
    public MemoryHandler(FunctionHandler functionHandler, boolean checkPointerValidity) {
    	m_functionHandler = functionHandler;
        this.sizeofConsts = new LinkedHashSet<String>();
        this.axioms = new LinkedHashSet<Axiom>();
        this.constants = new LinkedHashSet<ConstDeclaration>();
		this.mallocedAuxPointers = new LinkedScopedHashMap<LocalLValue, Integer>();
    	m_PointerBaseValidity = 
				(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).
				getEnum(PreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, POINTER_BASE_VALIDITY.class);
    	m_PointerAllocated = 
				(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).
				getEnum(PreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, POINTER_ALLOCATED.class);
    	m_CheckFreeValid = 
				(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).
				getBoolean(PreferenceInitializer.LABEL_CHECK_FREE_VALID);
		m_CheckMallocNonNegative = 
				(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).
				getBoolean(PreferenceInitializer.LABEL_CHECK_MallocNonNegative);
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
        VarList fBase = new VarList(tuLoc, new String[] { SFO.POINTER_BASE },
                intType);
        VarList fOffset = new VarList(tuLoc,
                new String[] { SFO.POINTER_OFFSET }, intType);
        VarList[] fields = new VarList[] { fBase, fOffset };
        ASTType pointerType = new StructType(tuLoc, new InferredType(
                Type.Struct), fields);
        // Pointer is non-finite, right? (ZxZ)..
        decl.add(new TypeDeclaration(tuLoc, new Attribute[0], false, 
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
        	//The name of the sizeof constants is determined by the name of the
        	//Ctype. Names of primitive CTypes are written in uppercase.
        	//Names of our boogie types are written in lowercase.
        	//Our convention is to use uppercase.
        	String CtypeCompatibleId;
        	if (tName[i].equals(SFO.POINTER)) {
        		CtypeCompatibleId = SFO.POINTER;
        	} else {
        		CtypeCompatibleId = tName[i].toUpperCase();
        	}
            declareSizeOf(l, CtypeCompatibleId);
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
            VariableLHS[] modified = new VariableLHS[tName.length];
            for (int j = 0; j < modified.length; j++) {
                modified[j] = new VariableLHS(l, SFO.MEMORY + "_" + tName[j]);
            }
            
            
            ArrayList<Specification> swrite = new ArrayList<Specification>();
            
            if (m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSERTandASSUME 
            		|| m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSUME) {
            	// requires #valid[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(l, false,
                			new ArrayAccessExpression(l, boolIT, valid,
                					idcWrite));
            	} else {
            		assert m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSUME;
            		specValid = new RequiresSpecification(l, true,
                			new ArrayAccessExpression(l, boolIT, valid,
                					idcWrite));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	swrite.add(specValid);
            }
            Expression ptrOff = new StructAccessExpression(l, intIT, idPtr,
                    SFO.POINTER_OFFSET);
            Expression ptrBase = new StructAccessExpression(l, intIT, idPtr,
                    SFO.POINTER_BASE);
            Expression length = new ArrayAccessExpression(l,
                    new IdentifierExpression(l, SFO.LENGTH),
                    new Expression[] { ptrBase });
            
            if (m_PointerAllocated == POINTER_ALLOCATED.ASSERTandASSUME 
            		|| m_PointerAllocated == POINTER_ALLOCATED.ASSUME) {
            	// requires #sizeof~$Pointer$ + #ptr!offset <=
            	// #length[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerAllocated == POINTER_ALLOCATED.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(l, false,
                			new BinaryExpression(l, Operator.COMPLEQ,
                					new BinaryExpression(l, Operator.ARITHPLUS,
                							new IdentifierExpression(l, SFO.SIZEOF
                							+ CtypeCompatibleId), ptrOff), length));
            	} else {
            		assert m_PointerAllocated == POINTER_ALLOCATED.ASSUME;
            		specValid = new RequiresSpecification(l, true,
                			new BinaryExpression(l, Operator.COMPLEQ,
                					new BinaryExpression(l, Operator.ARITHPLUS,
                							new IdentifierExpression(l, SFO.SIZEOF
                							+ CtypeCompatibleId), ptrOff), length));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	swrite.add(specValid);
            }
            swrite.add(new ModifiesSpecification(l, false, modified));
            for (int j = 0; j < modified.length; j++) {
                // ensures #memory_int == old(#valid)[~addr!base := false];
                Expression memA = new IdentifierExpression(l, SFO.MEMORY + "_"
                        + tName[j]);
                if (i == j) {
                    swrite.add(new EnsuresSpecification(
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
                                                    memA), idc, idVal))));
                } else {
                    Expression aae = new ArrayAccessExpression(l, memA, idc);
                    swrite.add(new EnsuresSpecification(
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
                                                    memA), idc, aae))));
                }
                
            }
            decl.add(new Procedure(l, new Attribute[0], nwrite, new String[0],
                    inWrite, new VarList[0], swrite.toArray(new Specification[0]), null));
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
            					new VariableLHS[] { new VariableLHS(l, tmpVar) });
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
            ArrayList<Specification> sread = new ArrayList<Specification>();
            
            if (m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSERTandASSUME 
            		|| m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSUME) {
            	// requires #valid[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(l, false,
                			new ArrayAccessExpression(l, boolIT, valid,
                					idcWrite));
            	} else {
            		assert m_PointerBaseValidity == POINTER_BASE_VALIDITY.ASSUME;
            		specValid = new RequiresSpecification(l, true,
                			new ArrayAccessExpression(l, boolIT, valid,
                					idcWrite));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	sread.add(specValid);
            }
            
            if (m_PointerAllocated == POINTER_ALLOCATED.ASSERTandASSUME || 
            		m_PointerAllocated == POINTER_ALLOCATED.ASSUME) {
            	// requires #sizeof~$Pointer$ + #ptr!offset <=
            	// #length[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerAllocated == POINTER_ALLOCATED.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(l, false, new BinaryExpression(l,
                			Operator.COMPLEQ, new BinaryExpression(l,
                					Operator.ARITHPLUS,
                					new IdentifierExpression(l, SFO.SIZEOF
                							+ CtypeCompatibleId), ptrOff), length));
            	} else {
            		assert m_PointerAllocated == POINTER_ALLOCATED.ASSUME;
            		specValid = new RequiresSpecification(l, true, new BinaryExpression(l,
                			Operator.COMPLEQ, new BinaryExpression(l,
                					Operator.ARITHPLUS,
                					new IdentifierExpression(l, SFO.SIZEOF
                							+ CtypeCompatibleId), ptrOff), length));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	sread.add(specValid);
            }
            
           	Expression arr = new IdentifierExpression(l, SFO.MEMORY + "_" + tName[i]);
           	Expression arrE = new ArrayAccessExpression(l, arr, idc);
           	Expression valueE = new IdentifierExpression(l, value);
           	Expression equality = new BinaryExpression(l, Operator.COMPEQ, valueE, arrE);
           	sread.add(new EnsuresSpecification(l, false, equality));

            decl.add(new Procedure(l, new Attribute[0], nread, new String[0],
                    inRead, outRead, sread.toArray(new Specification[0]), null));
            if (m_AddImplementation) {
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
    private ArrayList<Declaration> declareFree(final ILocation tuLoc) {
        InferredType intIT = new InferredType(Type.Integer);
        InferredType boolIT = new InferredType(Type.Boolean);
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        // procedure ~free(~addr:$Pointer$) returns();
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
        
        ArrayList<Specification> specFree = new ArrayList<Specification>();
        
        if (m_CheckFreeValid) {
        	Check check = new Check(Spec.MEMORY_FREE);
        	boolean free = false;
        	RequiresSpecification offsetZero = new RequiresSpecification(
        			tuLoc, free, new BinaryExpression(tuLoc, Operator.COMPEQ, 
        					addrOffset, nr0));
            check.addToNodeAnnot(offsetZero);
            specFree.add(offsetZero);
            RequiresSpecification baseValid = new RequiresSpecification(
                    tuLoc,
                    free,
                    new ArrayAccessExpression(tuLoc, boolIT, valid, idcFree));
            check.addToNodeAnnot(baseValid);
            specFree.add(baseValid);
            specFree.add(new EnsuresSpecification(tuLoc, false, new BinaryExpression(
                    tuLoc, Operator.COMPEQ, valid,
                    new ArrayStoreExpression(tuLoc, new UnaryExpression(
                            tuLoc, UnaryExpression.Operator.OLD, valid),
                            idcFree, bLFalse))));
            specFree.add(new ModifiesSpecification(tuLoc, false,
                    new VariableLHS[] { new VariableLHS(tuLoc, SFO.VALID) }));
        }
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.FREE,
                new String[0], new VarList[] { new VarList(tuLoc,
                        new String[] { ADDR }, POINTER_TYPE) }, new VarList[0],
                specFree.toArray(new Specification[0]), null));
        
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
    private ArrayList<Declaration> declareMalloc(final ILocation tuLoc) {
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
        Expression res = new IdentifierExpression(tuLoc, pointerIT, SFO.RES, null);
        Expression length = new IdentifierExpression(tuLoc, SFO.LENGTH);
        Expression[] idcMalloc = new Expression[] { new StructAccessExpression(
                tuLoc, intIT, res, SFO.POINTER_BASE) };
        Expression bLTrue = new BooleanLiteral(tuLoc, boolIT, true);
        IdentifierExpression size = new IdentifierExpression(tuLoc, intIT, SIZE, null);
        List<Specification> specMalloc = new ArrayList<Specification>();
        if (m_CheckMallocNonNegative) {
        	RequiresSpecification nonNegative = new RequiresSpecification(tuLoc,
        			false, new BinaryExpression(tuLoc, Operator.COMPGEQ, size, nr0));
        	nonNegative.getPayload().getAnnotations().put(
        		Check.getIdentifier(), new Check(Check.Spec.MALLOC_NONNEGATIVE));
        	specMalloc.add(nonNegative);
        }
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ,
                        new ArrayAccessExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc), bLFalse)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ, valid,
                        new ArrayStoreExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc, bLTrue))));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ,
                        new StructAccessExpression(tuLoc, intIT, res,
                                SFO.POINTER_OFFSET), nr0)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPNEQ,
                        new StructAccessExpression(tuLoc, intIT, res,
                                SFO.POINTER_BASE), nr0)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                new BinaryExpression(tuLoc, Operator.COMPEQ, length,
                        new ArrayStoreExpression(tuLoc, new UnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, length),
                                idcMalloc, size))));
        specMalloc.add(new ModifiesSpecification(tuLoc, false, new VariableLHS[] {
                new VariableLHS(tuLoc, SFO.VALID), 
                new VariableLHS(tuLoc, SFO.LENGTH) }));
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.MALLOC,
                new String[0], new VarList[] { new VarList(tuLoc,
                        new String[] { SIZE }, intType) },
                new VarList[] { new VarList(tuLoc, new String[] { SFO.RES },
                        POINTER_TYPE) }, specMalloc.toArray(new Specification[0]), null));
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
        			new LeftHandSide[] { new VariableLHS(tuLoc, pointerIT, SFO.RES, null) },
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
            throw new IncorrectSyntaxException(loc, msg);
        }
        String cId = main.cHandler.getSymbolTable().getCID4BoogieID(bId, loc);
        CType cvar = main.cHandler.getSymbolTable().get(cId, loc)
                .getCVariable();
        if (!isPointer(cvar) && !(main.cHandler.isHeapVar(bId))) {
            String msg = "Cannot free the non pointer variable " + cId;
            throw new IncorrectSyntaxException(loc, msg);
        }
        // Further checks are done in the precondition of ~free()!
        // ~free(E);
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        stmt.add(new CallStatement(loc, false, new VariableLHS[0], SFO.FREE,
                new Expression[] { e }));
        // add required information to function handler.
        if (fh.getCurrentProcedureID() != null) {
            LinkedHashSet<String> mgM = new LinkedHashSet<String>();
            mgM.add(SFO.VALID);
            if (!fh.getModifiedGlobals().containsKey(SFO.FREE)) {
                fh.getModifiedGlobals().put(SFO.FREE, mgM);
                fh.getCallGraph().put(SFO.FREE, new LinkedHashSet<String>());
            }
            fh.getCallGraph().get(fh.getCurrentProcedureID()).add(SFO.FREE);
        }
		Map<VariableDeclaration, ILocation> emptyAuxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>(0);
		assert (main.isAuxVarMapcomplete(decl, emptyAuxVars));
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }
    
    /**
     * Returns true iff ctype is
     * <ul>
     * <li> of type CPointer or
     * <li> of type CNamed and the mapped type is CPointer.
     * </ul>
     */
    private boolean isPointer(CType ctype) {
    	CType ut = ctype.getUnderlyingType();
    	return ut instanceof CPointer || ut instanceof CArray;
    }

    /**
     * Creates a function call expression for the ~malloc(size) function!
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param fh
     *            a reference to the FunctionHandler - required to add
     *            information to the call graph.
     * @param size
     *            the expression referring to size of the memory to be
     *            allocated.
     * @param loc
     *            Location for errors and new nodes in the AST.
     * @return a function call expression for ~malloc(size).
     */
    public ResultExpression getMallocCall(Dispatcher main, FunctionHandler fh,
            Expression size, CACSLLocation loc) {
    	String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MALLOC);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, MemoryHandler.POINTER_TYPE, loc);
        
        ResultExpression mallocRex = getMallocCall(main, fh, size, 
        		new LocalLValue(new VariableLHS(loc, tmpId), 
        				new CPointer(new CPrimitive(PRIMITIVE.VOID))), loc);
        
        mallocRex.auxVars.put(tVarDecl, loc);
        mallocRex.decl.add(tVarDecl);
        
        
		assert (main.isAuxVarMapcomplete(mallocRex.decl, mallocRex.auxVars));
		return mallocRex;
    }

    public ResultExpression getMallocCall(Dispatcher main,
			FunctionHandler fh, Expression size,
			LocalLValue resultPointer, ILocation loc) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();

        Expression[] args = new Expression[] { size };
        
        //TODO: extract this block and the one below to make the other getMallocCall nicer
//        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MALLOC);
//        InferredType tmpIType = new InferredType(Type.Pointer);
//        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, tmpIType, loc);
//        auxVars.put(tVarDecl, loc);
//        decl.add(tVarDecl);
        
        stmt.add(new CallStatement(loc, false, new VariableLHS[] { (VariableLHS) resultPointer.getLHS() },
                SFO.MALLOC, args));
        
        //TODO: extract this block and the one above to make the other getMallocCall nicer
//        Expression e = new IdentifierExpression(loc, it, tmpId);
        
        // add required information to function handler.
        if (fh.getCurrentProcedureID() != null) {
            LinkedHashSet<String> mgM = new LinkedHashSet<String>();
            mgM.add(SFO.VALID);
            mgM.add(SFO.LENGTH);
            if (!fh.getModifiedGlobals().containsKey(SFO.MALLOC)) {
                fh.getModifiedGlobals().put(SFO.MALLOC, mgM);
                fh.getCallGraph().put(SFO.MALLOC, new LinkedHashSet<String>());
            }
            fh.getCallGraph().get(fh.getCurrentProcedureID()).add(SFO.MALLOC);
        }
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>();
        return new ResultExpression(stmt, resultPointer, decl, auxVars);//FIXME pointsToType??
	}

	/**
     * Calculate the sizeof constants for the given CType.
     * 
     * @param cvar
     *            the CVariable to work on.
     * @return a reference to the constant, holding sizeof cvar.
     */
    public IdentifierExpression calculateSizeOf(CType cvar, ILocation loc) {
        assert cvar != null;
//        ILocation loc = cvar.getCASTLocation();
        ASTType intT = new PrimitiveType(loc, SFO.INT);
        String id = SFO.SIZEOF + cvar.toString();
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
                Expression valSize = calculateSizeOf(ca.getValueType(), loc);
                Expression nrElem = new IntegerLiteral(loc, "1");
                for (Expression dim : ca.getDimensions()) 
                	nrElem = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, nrElem, dim, loc);
                Expression size = new BinaryExpression(loc, Operator.ARITHMUL,
                        nrElem, valSize);
                Expression f = new BinaryExpression(loc, Operator.COMPEQ, idex,
                        size);
                this.axioms.add(new Axiom(loc, attr, f));
            } else if (cvar instanceof CStruct) {
                CStruct cs = (CStruct) cvar;
                if (cs.isIncomplete()) {
                	// do nothing
                } else {
                	Expression nextOffset = new IntegerLiteral(loc, SFO.NR0);
                	for (int i = 0; i < cs.getFieldCount(); i++) {
                		CType csf = cs.getFieldTypes()[i];
                		String csfId = cs.getFieldIds()[i];
                		String oId = SFO.OFFSET + cvar.toString() + "~" + csfId;
                		this.constants.add(new ConstDeclaration(loc, attr, false,
                				new VarList(loc, new String[] { oId }, intT), null,
                				false));
                		Expression offIdEx = new IdentifierExpression(loc, oId);
                		Expression offsetOfField = null;
//                		if (cvar instanceof CUnion) {//in a union every field begins at 0
//                			//(optimization: don't use so many constants where all are 0, but this way it is more 
//                			//consisten with struct treatment, thus easier, for now)
//                			offsetOfField = new BinaryExpression(loc, Operator.COMPEQ,
//                					offIdEx, new IntegerLiteral(loc, SFO.NR0));
//                		} else {
                		offsetOfField = new BinaryExpression(loc, Operator.COMPEQ,
                					offIdEx, nextOffset);
//                		}
                		this.axioms.add(new Axiom(loc, attr, offsetOfField));
                		Expression fieldSize = calculateSizeOf(csf, loc);
                		
                		if (cvar instanceof CUnion) {
                			this.axioms.add(new Axiom(loc, attr, 
                					new BinaryExpression(loc, Operator.COMPGEQ, idex, fieldSize)));
                		} else {//only in the struct case, the offsets grow, in the union case they stay at 0
                			nextOffset = new BinaryExpression(loc, Operator.ARITHPLUS,
                					nextOffset, fieldSize);
                		}
                	}
                	if (!(cvar instanceof CUnion)) { //we have a normal struct
                		// add an axiom : sizeof cvar (>)= nextOffset
                		Expression f = new BinaryExpression(loc, Operator.COMPGEQ,
                				idex, nextOffset);
                		this.axioms.add(new Axiom(loc, attr, f));
                	}
                }
            } else if (cvar instanceof CNamed) {
                // add an axiom, binding the sizeof of the named type to
                // the sizeof of the underlying type
                CNamed cn = ((CNamed) cvar);
                Expression e = calculateSizeOf(cn.getUnderlyingType(), loc);
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
    
//    /**
//     * Checks, if an accessed pointer points to a valid location in memory.
//     * 
//     * @param idx
//     *            the pointer to check.
//     * @return an assert statement that checks, whether the accessed memory
//     *         location is valid.
//     */
//    public Statement checkValidityOfAccess(Expression idx) {
//        assert idx.getType() instanceof InferredType
//                && ((InferredType) idx.getType()).getType() == Type.Pointer;
//        // assert #valid[idx!base];
//        ILocation loc = idx.getLocation();
//        Expression array = new IdentifierExpression(loc, SFO.VALID);
//        Expression idxBase = new StructAccessExpression(loc, idx,
//                SFO.POINTER_BASE);
//        Expression formula = new ArrayAccessExpression(loc, array,
//                new Expression[] { idxBase });
//        assert loc instanceof CACSLLocation;
//        CACSLLocation assertLoc = new CACSLLocation((CACSLLocation) loc,
//                new Check(Check.Spec.INVALID_MEMORY_ACCESS));
//        return new AssertStatement(assertLoc, formula);
//    }
    

    /**
     * Generates a call of the read procedure and writes the returned value to a
     * temp variable, returned in the expression of the returned
     * ResultExpression.
     * Note that we only read simple types from the heap -- when reading e.g. an  
     * array, we have to make readCalls for each cell.
     * 
     * @param main
     *            a reference to the main dispatcher.
     * @param tPointer
     *            the address to read from.
     * @param pointerCType
     *            the CType of the pointer in tPointer
     * @return all declarations and statements required to perform the read,
     *         plus an identifierExpression holding the read value.
     */
    public ResultExpression getReadCall(Dispatcher main,
    		RValue address) {
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
        ILocation loc = (ILocation) address.getValue().getLocation();
        
        ASTType heapType = getHeapTypeOfLRVal(address);
        
        String heapTypeName = "";
        if (heapType.equals(MemoryHandler.POINTER_TYPE)) {
        	heapTypeName = SFO.POINTER;
        } else {
        	heapTypeName = ((PrimitiveType) heapType).getName();
        }
        
        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, heapType, loc);
        auxVars.put(tVarDecl, loc);
        decl.add(tVarDecl);
        VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, tmpId) };
        CallStatement call = new CallStatement(loc, false, lhs, "read~" + heapTypeName,//heapType.toString(),
                new Expression[] { address.getValue() });
        for (Overapprox overapprItem : overappr) {
            call.getPayload().getAnnotations().put(Overapprox.getIdentifier(),
                    overapprItem);
        }
        stmt.add(call);
		assert (main.isAuxVarMapcomplete(decl, auxVars));
        return new ResultExpression(stmt, 
        		new RValue(new IdentifierExpression(loc, tmpId), address.cType),
        		decl, auxVars, overappr);
    }
    
    ASTType getHeapTypeOfLRVal(LRValue lrVal) {
    	CType ct = lrVal.cType;
    	
//    	if (/*lrVal.isOnHeap*/ lrVal.isPointer)
//    		return POINTER_TYPE;
    	
    	if (lrVal.isBoogieBool)
    		return new PrimitiveType(lrVal.getValue().getLocation(), SFO.BOOL);
    	
    	CType ut = ct;
    	if (ut instanceof CNamed)
    		ut = ((CNamed) ut).getUnderlyingType();
    	
    	if (ut instanceof CPrimitive) {
			CPrimitive cp = (CPrimitive) ut;
			switch (cp.getGeneralType()) {
			case INTTYPE:
				return new PrimitiveType(lrVal.getValue().getLocation(), SFO.INT);
			case FLOATTYPE:
				return new PrimitiveType(lrVal.getValue().getLocation(), SFO.REAL);
			default:
				throw new UnsupportedSyntaxException(null, "unsupported cType " + ct);
			}
		} else if (ut instanceof CPointer) {
			return MemoryHandler.POINTER_TYPE;
		} else if (ut instanceof CNamed) {
			assert false : "This should not be the case as we took the underlying type.";
			throw new UnsupportedSyntaxException(null, "non-heap type?: " + ct);
		} else {
			throw new UnsupportedSyntaxException(null, "non-heap type?: " + ct);
		}
    }

    /**
     * Generates a procedure call to writeT(val, ptr), writing val to the
     * according memory array.
     * (for the C-methode the argument order is value, target, for this
     * method it's the other way around)
     * 
     * @param hlv
     *            the HeapLvalue containing the address to write to
     * @param rval
     *            the value to write.
     * @return the required Statements to perform the write.
     */
    public ArrayList<Statement> getWriteCall(HeapLValue hlv, RValue rval) {
    	
    	for (String t : new String[] { SFO.INT, SFO.POINTER,
				SFO.REAL, SFO.BOOL }) {
			m_functionHandler.getModifiedGlobals()
					.get(m_functionHandler.getCurrentProcedureID())
					.add(SFO.MEMORY + "_" + t);
		}
    	
        ILocation loc = hlv.getAddress().getLocation();
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        
        CType rType = rval.cType;
        if (rType instanceof CNamed)
        	rType = ((CNamed) rType).getUnderlyingType();
        
        String t = SFO.EMPTY;
        if (rType instanceof CPrimitive) {
        	switch (((CPrimitive) rType).getGeneralType()) {
        	case INTTYPE:
        		t = SFO.INT;	        
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + t,
        				new Expression[] { rval.getValue(), hlv.getAddress() }));
        		break;
        	case FLOATTYPE:
        		t = SFO.REAL;	        
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + t,
        				new Expression[] { rval.getValue(), hlv.getAddress() }));
        		break;	
        	default:
        		throw new UnsupportedSyntaxException(loc, "we don't recognize this type");
        	}
        } else if (rType instanceof CPointer) {
        	t = SFO.POINTER;	        
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + t,
        				new Expression[] { rval.getValue(), hlv.getAddress() }));
        } else if (rType instanceof CStruct) {
        	CStruct rStructType = (CStruct) rType;
        	for (String fieldId : rStructType.getFieldIds()) {
        		Expression startAddress = hlv.getAddress();
    			Expression newStartAddressBase = null;
    			Expression newStartAddressOffset = null;
    			if (startAddress instanceof StructConstructor) {
    				newStartAddressBase = ((StructConstructor) startAddress).getFieldValues()[0];
    				newStartAddressOffset = ((StructConstructor) startAddress).getFieldValues()[1];
    			} else {
    				newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
    				newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
    			}
        		
        		CType fieldType = rStructType.getFieldType(fieldId);
        		StructAccessExpression sae = new StructAccessExpression(loc, 
        				rval.getValue(), fieldId);
        		Expression fieldOffset = 
						StructHandler.getStructOrUnionOffsetConstantExpression(loc, this, fieldId, rStructType);
        		Expression newOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus, 
        				newStartAddressOffset,
        				fieldOffset, loc);
        		HeapLValue fieldHlv = new HeapLValue(
        				constructPointerFromBaseAndOffset(newStartAddressBase,
        				newOffset, loc), fieldType);
        		stmt.addAll(getWriteCall(fieldHlv, new RValue(sae, fieldType)));
        	}
        	
        } else if (rType instanceof CArray) {
        	throw new UnsupportedSyntaxException(loc, "todo: write to arrays on the heap");
        } else
        	throw new UnsupportedSyntaxException(loc, "we don't recognize this type");
		
        return stmt;
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
//        assert ptr.getType() instanceof InferredType;
//        assert ((InferredType) ptr.getType()).getType() == Type.Pointer;
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
		Map<VariableDeclaration, ILocation> emptyAuxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>(0);
        return new ResultExpression(stmt, null, decl, emptyAuxVars);
    }
    
    /**
     * Takes a pointer Expression and returns the pointers base address.
     * If it is already given as a struct, then the first field is returned,
     * otherwise a StructAccessExpression pointer!base is returned.
     * @param pointer
     */
	public static Expression getPointerBaseAddress(Expression pointer, ILocation loc) {
	    if (pointer instanceof StructConstructor) {
            return ((StructConstructor) pointer).getFieldValues()[0];
        }
		return new StructAccessExpression(loc, new InferredType(Type.Integer), pointer, "base");
	}
	
	/**
     * Takes a pointer Expression and returns the pointers base address.
     * If it is already given as a struct, then the second field is returned,
     * otherwise a StructAccessExpression pointer!offset is returned.
     * @param pointer
     */
	public static Expression getPointerOffset(Expression pointer, ILocation loc) {
	    if (pointer instanceof StructConstructor) {
            return ((StructConstructor) pointer).getFieldValues()[1];
        }
		return new StructAccessExpression(loc, new InferredType(Type.Integer), pointer, "offset");
	}
	
	public static StructConstructor constructPointerFromBaseAndOffset(Expression base, Expression offset, ILocation loc) {
		return new StructConstructor(loc, new InferredType(Type.Pointer), 
				new String[]{"base", "offset"}, new Expression[]{base, offset}); 
	}
	
	@Deprecated //use NULL instead
	public static StructConstructor constructNullPointer(ILocation loc) {
	    return new StructConstructor(loc, new InferredType(Type.Pointer), 
                new String[]{"base", "offset"}, new Expression[]{new IntegerLiteral(loc, "0"), new IntegerLiteral(loc, "0")}); 
    }
	/**
	 * Takes a loop or function body and inserts mallocs and frees for all the identifiers in this.mallocedAuxPointers
	 */
	public ArrayList<Statement> insertMallocs(Dispatcher main, ILocation loc, ArrayList<Statement> block) {
		ArrayList<Statement> mallocs = new ArrayList<Statement>();
		for (LocalLValue llv : this.mallocedAuxPointers.currentScopeKeys()) 
			mallocs.addAll(this.getMallocCall(main, m_functionHandler, this.calculateSizeOf(llv.cType, loc), llv, loc).stmt);
		ArrayList<Statement> frees = new ArrayList<Statement>();
		for (LocalLValue llv : this.mallocedAuxPointers.currentScopeKeys())  //frees are inserted in handleReturnStm
			frees.addAll(this.getFreeCall(main, m_functionHandler, llv.getValue(), loc).stmt);
		ArrayList<Statement> newBlockAL = new ArrayList<Statement>();
		newBlockAL.addAll(mallocs);
		newBlockAL.addAll(block);
		newBlockAL.addAll(frees);
		return newBlockAL;
	}
	
	public void addMallocedAuxPointer(Dispatcher main, LocalLValue thisLVal) {
//		if (!main.typeHandler.isStructDeclaration())
			this.mallocedAuxPointers.put(thisLVal, mallocedAuxPointers.getActiveScopeNum());
	}
	
	public LinkedScopedHashMap<LocalLValue, Integer> getMallocedAuxPointers() {
		return mallocedAuxPointers;
	}

}
