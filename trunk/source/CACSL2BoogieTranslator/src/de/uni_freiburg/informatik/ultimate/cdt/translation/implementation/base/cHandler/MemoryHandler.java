/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 * Class that handles translation of memory related operations.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
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
     * Add also implementations of malloc, free, write and read functions.
     * TODO: details
     */
	private static final boolean m_AddImplementation = false;
	
	
	private final POINTER_CHECKMODE m_PointerBaseValidity;
	private final POINTER_CHECKMODE m_checkPointerSubtractionAndComparisonValidity;
	private final POINTER_CHECKMODE m_PointerAllocated;
	private final boolean m_CheckFreeValid;
	private final boolean m_CheckMallocNonNegative;
	
	public boolean isIntArrayRequiredInMM;
	public boolean isFloatArrayRequiredInMM;
	public boolean isPointerArrayRequiredInMM;
	
	//needed for adding modifies clauses
	private FunctionHandler m_functionHandler;

	/**
	 * This set contains those pointers that we have to malloc at the beginning
	 *  of the current scope;
	 */
	private LinkedScopedHashMap<LocalLValueILocationPair, Integer> variablesToBeMalloced;
	/**
	 * This set contains those pointers that we have to 
	 * free at the end of the current scope;
	 */
	LinkedScopedHashMap<LocalLValueILocationPair, Integer> variablesToBeFreed;

//	private boolean noMemArrays;
	
	private boolean declareMemCpy = false;
	
	public void setDeclareMemCpy() {
		declareMemCpy = true;
	}
	
	private final AExpressionTranslation m_ExpressionTranslation;
	
	private final TypeSizeAndOffsetComputer m_TypeSizeAndOffsetComputer;
	
	
	/**
     * Constructor.
     * @param checkPointerValidity 
	 * @param typeSizeComputer 
     */
    public MemoryHandler(FunctionHandler functionHandler, boolean checkPointerValidity, 
    		TypeSizeAndOffsetComputer typeSizeComputer, AExpressionTranslation expressionTranslation) {
    	m_functionHandler = functionHandler;
    	m_ExpressionTranslation = expressionTranslation;
		this.variablesToBeMalloced = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		this.variablesToBeFreed = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		//read preferences from settings
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		
		m_PointerBaseValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, POINTER_CHECKMODE.class);
    	m_PointerAllocated = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, POINTER_CHECKMODE.class);
    	m_CheckFreeValid = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		m_CheckMallocNonNegative = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MallocNonNegative);
    	m_checkPointerSubtractionAndComparisonValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY, POINTER_CHECKMODE.class);
		
		isIntArrayRequiredInMM = false;
		isFloatArrayRequiredInMM = false;
		isPointerArrayRequiredInMM = false;
		m_TypeSizeAndOffsetComputer = typeSizeComputer;
    }
    
    
    public Expression calculateSizeOf(ILocation loc, CType cType) {
    	return m_TypeSizeAndOffsetComputer.constructBytesizeExpression(loc, cType);
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
        ASTType pointerComponentType = main.typeHandler.ctype2asttype(tuLoc, 
        		m_ExpressionTranslation.getCTypeOfPointerComponents());
        ASTType intArrayType = main.typeHandler.ctype2asttype(tuLoc, 
        		m_ExpressionTranslation.getCTypeOfIntArray());
        ASTType realArrayType = main.typeHandler.ctype2asttype(tuLoc, 
        		m_ExpressionTranslation.getCTypeOfFloatingArray());
       

        // NULL Pointer
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { new VarList(tuLoc, new String[] { SFO.NULL },
                        main.typeHandler.constructPointerType(tuLoc)) }));
        // to add a type declaration for "real"
        // decl.add(new TypeDeclaration(tuLoc, new Attribute[0], false,
        // SFO.REAL, new String[0]));
        
        //declare the arrays that will model the heap
        
        // add memory arrays and access procedures
        ArrayList<String> allMMArrayNames = new ArrayList<>();
        ArrayList<ASTType> allMMArrayTypes = new ArrayList<>();
        if (isIntArrayRequiredInMM) {
        	allMMArrayNames.add(SFO.INT);
        	allMMArrayTypes.add(intArrayType);
        }
        if (isFloatArrayRequiredInMM) {
        	allMMArrayNames.add(SFO.REAL);
        	allMMArrayTypes.add(realArrayType);
        }
        if (isPointerArrayRequiredInMM) {
        	allMMArrayNames.add(SFO.POINTER);
        	allMMArrayTypes.add(main.typeHandler.constructPointerType(tuLoc));
        }
        String[] namesOfAllMemoryArrayTypes = allMMArrayNames.toArray(new String[0]);
        ASTType[] astTypesOfAllMemoryArrayTypes = allMMArrayTypes.toArray(new ASTType[0]);
        
//        if (namesOfAllMemoryArrayTypes.length == 0) { 
//        	noMemArrays = true;
////        	return decl;//if we reach here, mmRequired == true --> we need valid + length (one usecase: we malloc but don't use something..)
//        }
        
        decl.addAll(declareSomeMemoryArrays(tuLoc, main, namesOfAllMemoryArrayTypes, astTypesOfAllMemoryArrayTypes));
       
        // var #valid : [int]bool;
        ASTType validType = new ArrayType(tuLoc, new String[0],
                new ASTType[] { pointerComponentType }, new PrimitiveType(tuLoc, "bool"));
        VarList vlV = new VarList(tuLoc, new String[] { SFO.VALID }, validType);
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { vlV }));
        // var #length : [int]int;
        ASTType lengthType = new ArrayType(tuLoc, new String[0],
                new ASTType[] { pointerComponentType }, pointerComponentType);
        VarList vlL = new VarList(tuLoc, new String[] { SFO.LENGTH },
                lengthType);
        decl.add(new VariableDeclaration(tuLoc, new Attribute[0],
                new VarList[] { vlL }));
        decl.addAll(declareFree(main, tuLoc));
        decl.addAll(declareMalloc(main.typeHandler, tuLoc));
        if (declareMemCpy) {
        	decl.addAll(declareMemCpy(main, namesOfAllMemoryArrayTypes, astTypesOfAllMemoryArrayTypes));
        }
        return decl;
    }

    /**
     * Adds our implementation of the memcpy procedure to the boogie code.
     */
    private Collection<? extends Declaration> declareMemCpy(Dispatcher main,
    		String[] namesOfAllMemoryArrayTypes, ASTType[] astTypesOfAllMemoryArrayTypes) {
    	ArrayList<Declaration> memCpyDecl = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	VarList inPDest = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_DEST }, main.typeHandler.constructPointerType(ignoreLoc));
    	VarList inPSrc = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SRC }, main.typeHandler.constructPointerType(ignoreLoc));
    	VarList	inPSize = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SIZE }, new PrimitiveType(ignoreLoc, SFO.INT));
    	VarList[] inParams = new VarList[] { inPDest, inPSrc, inPSize };
    	
    	VarList[] outParams = new VarList[] { new VarList(ignoreLoc, new String[] { SFO.RES }, main.typeHandler.constructPointerType(ignoreLoc)) };

   			
    	ArrayList<VariableDeclaration> decl = new ArrayList<>();
    	ArrayList<Statement> stmt = new ArrayList<>();
    	
    	String loopCtr = main.nameHandler.getTempVarUID(SFO.AUXVAR.LOOPCTR);
		VarList lcvl = new VarList(ignoreLoc, new String[] { loopCtr }, new PrimitiveType(ignoreLoc, SFO.INT));
		VariableDeclaration loopCtrDec = new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { lcvl });
		decl.add(loopCtrDec);
		//initialize the counter to 0
		Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		stmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { new VariableLHS(ignoreLoc, loopCtr)}, 
				new Expression[] { zero }));
		
		IdentifierExpression ctrIdex = new IdentifierExpression(ignoreLoc, loopCtr);
		Expression condition = ExpressionFactory.newBinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLT, 
				ctrIdex,
				new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE));
		
		
		ArrayList<Statement> bodyStmt = new ArrayList<>();

		//make the assigments on the arrays
		Expression currentDest = ((CHandler) main.cHandler).doPointerArithmetic(main, IASTBinaryExpression.op_plus, ignoreLoc, 
					new IdentifierExpression(ignoreLoc, SFO.MEMCPY_DEST), 
					new RValue(ctrIdex, m_ExpressionTranslation.getCTypeOfPointerComponents()), 
					new CPrimitive(PRIMITIVE.VOID));
		Expression currentSrc = ((CHandler) main.cHandler).doPointerArithmetic(main, IASTBinaryExpression.op_plus, ignoreLoc, 
					new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SRC), 
					new RValue(ctrIdex, m_ExpressionTranslation.getCTypeOfPointerComponents()), 
					new CPrimitive(PRIMITIVE.VOID));

		// handle modifies
		ArrayList<VariableLHS> modifiesLHSs = new ArrayList<>();
		for (String name : namesOfAllMemoryArrayTypes) {
			String memArrayName = SFO.MEMORY + "_" + name;
			ArrayAccessExpression srcAcc = new ArrayAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, memArrayName), new Expression[] { currentSrc });
			ArrayLHS destAcc = new ArrayLHS(ignoreLoc, new VariableLHS(ignoreLoc, memArrayName), new Expression[] { currentDest });
			bodyStmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { destAcc }, new Expression[] { srcAcc }));
			modifiesLHSs.add(new VariableLHS(ignoreLoc, memArrayName));

			if (!m_functionHandler.getModifiedGlobals().containsKey(SFO.MEMCPY)){
				m_functionHandler.getModifiedGlobals().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			m_functionHandler.getModifiedGlobals().get(SFO.MEMCPY).add(memArrayName);
		}
		
		//increment counter
		VariableLHS ctrLHS = new VariableLHS(ignoreLoc, loopCtr);
		Expression one = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
		bodyStmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { ctrLHS }, 
				new Expression[] { constructPointerComponentAddition(ignoreLoc,
						ctrIdex, one) }));

		
		Statement[] whileBody = bodyStmt.toArray(new Statement[bodyStmt.size()]);
		
		WhileStatement whileStm = new WhileStatement(ignoreLoc, condition, new LoopInvariantSpecification[0], whileBody); 
		stmt.add(whileStm);
		
		Body procBody = new Body(ignoreLoc, 
				decl.toArray(new VariableDeclaration[decl.size()]), 
				stmt.toArray(new Statement[stmt.size()]));
		
		//make the specifications
		ArrayList<Specification> specs = new ArrayList<>();
		ModifiesSpecification modifies = new ModifiesSpecification(ignoreLoc, false, 
				 modifiesLHSs.toArray(new VariableLHS[modifiesLHSs.size()]));
		specs.add(modifies);
		
		Expression srcBase = new StructAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SRC),
                    SFO.POINTER_BASE);
		Expression destBase = new StructAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, SFO.MEMCPY_DEST),
                    SFO.POINTER_BASE);
	
		
        Expression valid = new IdentifierExpression(ignoreLoc, SFO.VALID);	
		if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME 
        		|| m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME) {
        	// requires #valid[#ptr!base];
        	RequiresSpecification specValidSrc = null;
        	RequiresSpecification specValidDest = null;
        	if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME) {
        		specValidSrc = new RequiresSpecification(ignoreLoc, false,
            			new ArrayAccessExpression(ignoreLoc, valid,
            					new Expression[] { srcBase }));
        		specValidDest = new RequiresSpecification(ignoreLoc, false,
            			new ArrayAccessExpression(ignoreLoc, valid,
            					new Expression[] { destBase }));
        	} else {
        		assert m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME;
        		specValidSrc = new RequiresSpecification(ignoreLoc, true,
            			new ArrayAccessExpression(ignoreLoc, valid,
            					new Expression[] { srcBase }));
        		specValidDest = new RequiresSpecification(ignoreLoc, true,
            			new ArrayAccessExpression(ignoreLoc, valid,
            					new Expression[] { destBase }));
        	}
        	Check check = new Check(Spec.MEMORY_DEREFERENCE);
        	check.addToNodeAnnot(specValidSrc);
        	specs.add(specValidSrc);
        	check.addToNodeAnnot(specValidDest);
        	specs.add(specValidDest);
        }
		Expression srcOffset = new StructAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SRC),
                    SFO.POINTER_OFFSET);
		Expression destOffset = new StructAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, SFO.MEMCPY_DEST),
                    SFO.POINTER_OFFSET);
//	
		Expression lengthSrc = new ArrayAccessExpression(ignoreLoc,
				new IdentifierExpression(ignoreLoc, SFO.LENGTH),
				new Expression[] { srcBase });
		Expression lengthDest = new ArrayAccessExpression(ignoreLoc,
				new IdentifierExpression(ignoreLoc, SFO.LENGTH),
				new Expression[] { srcBase });

		if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME 
				|| m_PointerAllocated == POINTER_CHECKMODE.ASSUME) {
			// requires #sizeof~$Pointer$ + #ptr!offset <=
					// #length[#ptr!base];
        	RequiresSpecification specLengthSrc = null;
        	RequiresSpecification specLengthDest = null;
			if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
				specLengthSrc = new RequiresSpecification(ignoreLoc, false,
						constructPointerComponentLessEqual(ignoreLoc, //TODO LT or LEQ?? (also below..)
								constructPointerComponentAddition(ignoreLoc,
										new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE),
										srcOffset), lengthSrc));
				specLengthDest = new RequiresSpecification(ignoreLoc, false,
						constructPointerComponentLessEqual(ignoreLoc,
								constructPointerComponentAddition(ignoreLoc,
										new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE),
										destOffset), lengthDest));
			} else {
				assert m_PointerAllocated == POINTER_CHECKMODE.ASSUME;
				specLengthSrc = new RequiresSpecification(ignoreLoc, true,
						constructPointerComponentLessEqual(ignoreLoc,
								constructPointerComponentAddition(ignoreLoc,
										new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE),
										srcOffset), lengthSrc));
				specLengthDest = new RequiresSpecification(ignoreLoc, true,
						constructPointerComponentLessEqual(ignoreLoc,
								constructPointerComponentAddition(ignoreLoc,
										new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE),
										destOffset), lengthDest));
			}
			Check check = new Check(Spec.MEMORY_DEREFERENCE);
			check.addToNodeAnnot(specLengthSrc);
			specs.add(specLengthSrc);
			check.addToNodeAnnot(specLengthDest);
			specs.add(specLengthDest);
		}	
   	
		//add the procedure declaration
     	Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], SFO.MEMCPY, new String[0], 
    			inParams, outParams, specs.toArray(new Specification[specs.size()]), null);
     	memCpyDecl.add(memCpyProcDecl);
     	
     	//add the procedure implementation
     	Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], SFO.MEMCPY, new String[0], 
    			inParams, outParams, null, procBody);
     	memCpyDecl.add(memCpyProc);
    	
		return memCpyDecl;
	}

    /**
     * Declares those of the memory arrays <code>#memory_int</code>,
     * <code>#memory_bool</code> (deprecated), <code>#memory_real</code> and
     * <code>#memory_$Pointer$</code>, that are listed in the arguments,
     * as well as read and write procedures for these arrays.
     * 
     * @param loc the location of the translation unit.
     * @param main 
     * @return the declarations for the memory arrays as well as read and write
     *         procedures for these arrays.
     */
	private ArrayList<Declaration> declareSomeMemoryArrays(final ILocation loc, Dispatcher main,
			 String[] namesOfAllMemoryArrayTypes,
			ASTType[] astTypesOfAllMemoryArrayTypes) {
		ArrayList<Declaration> decl = new ArrayList<>();
        ASTType intType = main.typeHandler.ctype2asttype(loc, m_ExpressionTranslation.getCTypeOfIntArray());
		for (int i = 0; i < namesOfAllMemoryArrayTypes.length; i++) {
        	String typeName = namesOfAllMemoryArrayTypes[i];
        	ASTType astType = astTypesOfAllMemoryArrayTypes[i];
        	//The name of the sizeof constants is determined by the name of the
        	//Ctype. Names of primitive CTypes are written in uppercase.
        	//Names of our boogie types are written in lowercase.
        	//Our convention is to use uppercase.
        	String CtypeCompatibleId;
        	if (typeName.equals(SFO.POINTER)) {
        		CtypeCompatibleId = SFO.POINTER;
        	} else {
        		CtypeCompatibleId = typeName.toUpperCase();
        	}
//            declareSizeOf(main, loc, CtypeCompatibleId, typeSizeConstants.useFixedTypeSizes());
            ASTType memoryType = new ArrayType(loc, new String[0],
                    new ASTType[] { main.typeHandler.constructPointerType(loc) }, astType);
            VarList vlM = new VarList(loc, new String[] { SFO.MEMORY + "_"
                    + typeName }, memoryType);
            decl.add(new VariableDeclaration(loc, new Attribute[0],
                    new VarList[] { vlM }));
            // create and add read and write procedure
            String value = "#value";
            String inPtr = "#ptr";
            String writtenTypeSize = "#sizeOfWrittenType"; //this is needed for the requires spec that adds this typesize once to make sure we don't write behind the memregion
            String readTypeSize = "#sizeOfReadType"; 
            Expression idVal = new IdentifierExpression(loc, value);
            Expression idPtr = new IdentifierExpression(loc, inPtr);
            Expression[] idc = new Expression[] { idPtr };
            String nwrite = "write~" + typeName;
            String nread = "read~" + typeName;
            VarList[] inWrite = new VarList[] {
                    new VarList(loc, new String[] { value }, astType),
                    new VarList(loc, new String[] { inPtr }, main.typeHandler.constructPointerType(loc)),
                    new VarList(loc, new String[] { writtenTypeSize }, intType) };
            Expression valid = new IdentifierExpression(loc, SFO.VALID);
            Expression addr = new IdentifierExpression(loc, inPtr);
            Expression addrBase = new StructAccessExpression(loc, addr,
                    SFO.POINTER_BASE);
            Expression[] idcWrite = new Expression[] { addrBase };
            VariableLHS[] modified = new VariableLHS[namesOfAllMemoryArrayTypes.length];
            for (int j = 0; j < modified.length; j++) {
                modified[j] = new VariableLHS(loc, SFO.MEMORY + "_" + namesOfAllMemoryArrayTypes[j]);
            }
            
            
            ArrayList<Specification> swrite = new ArrayList<Specification>();
            
            if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME 
            		|| m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME) {
            	// requires #valid[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(loc, false,
                			new ArrayAccessExpression(loc, valid,
                					idcWrite));
            	} else {
            		assert m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME;
            		specValid = new RequiresSpecification(loc, true,
                			new ArrayAccessExpression(loc, valid,
                					idcWrite));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	swrite.add(specValid);
            }
            Expression ptrOff = new StructAccessExpression(loc, idPtr,
                    SFO.POINTER_OFFSET);
            Expression ptrBase = new StructAccessExpression(loc, idPtr,
                    SFO.POINTER_BASE);
            Expression length = new ArrayAccessExpression(loc,
                    new IdentifierExpression(loc, SFO.LENGTH),
                    new Expression[] { ptrBase });
            
            if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME 
            		|| m_PointerAllocated == POINTER_CHECKMODE.ASSUME) {
            	// requires #sizeof~$Pointer$ + #ptr!offset <=
            	// #length[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(loc, false,
            				constructPointerComponentLessEqual(loc,
                					constructPointerComponentAddition(loc,
                							new IdentifierExpression(loc, writtenTypeSize),
//                							new IdentifierExpression(loc, SFO.SIZEOF + CtypeCompatibleId),
                					  ptrOff), length));
            	} else {
            		assert m_PointerAllocated == POINTER_CHECKMODE.ASSUME;
            		specValid = new RequiresSpecification(loc, true,
            				constructPointerComponentLessEqual(loc,
                					constructPointerComponentAddition(loc,
                							new IdentifierExpression(loc, writtenTypeSize),
//                							new IdentifierExpression(loc, SFO.SIZEOF + CtypeCompatibleId),
                							ptrOff), length));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	swrite.add(specValid);
            }
            swrite.add(new ModifiesSpecification(loc, false, modified));
            for (String s : namesOfAllMemoryArrayTypes) {
                // ensures #memory_int == old(#valid)[~addr!base := false];
                Expression memA = new IdentifierExpression(loc, SFO.MEMORY + "_"
                        + s);
                if (s.equals(typeName)) {
                    swrite.add(new EnsuresSpecification(
                            loc,
                            false,
                            ExpressionFactory.newBinaryExpression(
                                    loc,
                                    Operator.COMPEQ,
                                    memA,
                                    new ArrayStoreExpression(
                                            loc,
                                            ExpressionFactory.newUnaryExpression(
                                                    loc,
                                                    UnaryExpression.Operator.OLD,
                                                    memA), idc, idVal))));
                } else {
                    Expression aae = new ArrayAccessExpression(loc, memA, idc);
                    swrite.add(new EnsuresSpecification(
                            loc,
                            false,
                            ExpressionFactory.newBinaryExpression(
                                    loc,
                                    Operator.COMPEQ,
                                    memA,
                                    new ArrayStoreExpression(
                                            loc,
                                            ExpressionFactory.newUnaryExpression(
                                                    loc,
                                                    UnaryExpression.Operator.OLD,
                                                    memA), idc, aae))));
                }
                
            }
            decl.add(new Procedure(loc, new Attribute[0], nwrite, new String[0],
                    inWrite, new VarList[0], swrite.toArray(new Specification[swrite.size()]), null));
            if (m_AddImplementation) {
            	VariableDeclaration[] writeDecl = new VariableDeclaration[astTypesOfAllMemoryArrayTypes.length];
            	Statement[] writeBlock = new Statement[2 * astTypesOfAllMemoryArrayTypes.length - 1];
            	for (int j = 0, k = 0; j < astTypesOfAllMemoryArrayTypes.length; j++, k++) {
            		String tmpVar = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);	
            		writeDecl[j] = new VariableDeclaration(loc, new Attribute[0],
            				new VarList[] { new VarList(loc, new String[] { tmpVar },
            						astTypesOfAllMemoryArrayTypes[j]) });
            		VariableLHS arr = new VariableLHS(loc, SFO.MEMORY + "_"
            				+ namesOfAllMemoryArrayTypes[j]);
            		LeftHandSide[] arrL = new LeftHandSide[] { new ArrayLHS(loc, arr,
            				idc) };
            		if (namesOfAllMemoryArrayTypes[j].equals(typeName)) {
            			writeBlock[k] = new AssignmentStatement(loc, arrL,
            					new Expression[] { idVal });
            		} else {
            			writeBlock[k] = new HavocStatement(loc,
            					new VariableLHS[] { new VariableLHS(loc, tmpVar) });
            			writeBlock[++k] = new AssignmentStatement(loc, arrL,
            					new Expression[] { new IdentifierExpression(loc,
            							tmpVar) });
            		}
            	}
            	Body bwrite = new Body(loc, writeDecl, writeBlock);
            	decl.add(new Procedure(loc, new Attribute[0], nwrite, new String[0],
            			inWrite, new VarList[0], null, bwrite));
            }
            VarList[] inRead = new VarList[] { 
            		new VarList(loc, new String[] { inPtr }, main.typeHandler.constructPointerType(loc)),
            		new VarList(loc, new String[] { readTypeSize }, intType) };
            VarList[] outRead = new VarList[] { new VarList(loc,
                    new String[] { value }, astType) };
            ArrayList<Specification> sread = new ArrayList<Specification>();
            
            if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME 
            		|| m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME) {
            	// requires #valid[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(loc, false,
                			new ArrayAccessExpression(loc, valid,
                					idcWrite));
            	} else {
            		assert m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME;
            		specValid = new RequiresSpecification(loc, true,
                			new ArrayAccessExpression(loc, valid,
                					idcWrite));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	sread.add(specValid);
            }
            
            if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME || 
            		m_PointerAllocated == POINTER_CHECKMODE.ASSUME) {
            	// requires #sizeof~$Pointer$ + #ptr!offset <=
            	// #length[#ptr!base];
            	RequiresSpecification specValid;
            	if (m_PointerAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
            		specValid = new RequiresSpecification(loc, false, 
            				constructPointerComponentLessEqual(loc,
            						constructPointerComponentAddition(loc, 
                					new IdentifierExpression(loc, readTypeSize),
//                					new IdentifierExpression(loc, SFO.SIZEOF + CtypeCompatibleId),
                					ptrOff), length));
            	} else {
            		assert m_PointerAllocated == POINTER_CHECKMODE.ASSUME;
            		specValid = new RequiresSpecification(loc, true, 
            				constructPointerComponentLessEqual(loc,
            						constructPointerComponentAddition(loc, 
            						new IdentifierExpression(loc, readTypeSize),
//                					new IdentifierExpression(loc, SFO.SIZEOF + CtypeCompatibleId),
            						ptrOff), length));
            	}
            	Check check = new Check(Spec.MEMORY_DEREFERENCE);
            	check.addToNodeAnnot(specValid);
            	sread.add(specValid);
            }
            
           	Expression arr = new IdentifierExpression(loc, SFO.MEMORY + "_" + typeName);
           	Expression arrE = new ArrayAccessExpression(loc, arr, idc);
           	Expression valueE = new IdentifierExpression(loc, value);
           	Expression equality = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, valueE, arrE);
           	sread.add(new EnsuresSpecification(loc, false, equality));

            decl.add(new Procedure(loc, new Attribute[0], nread, new String[0],
                    inRead, outRead, sread.toArray(new Specification[0]), null));
            if (m_AddImplementation) {
            	Statement[] readBlock = new Statement[] { new AssignmentStatement(
            			loc, new LeftHandSide[] { new VariableLHS(loc, value) },
            			new Expression[] { arrE }) };
            	Body bread = new Body(loc, new VariableDeclaration[0], readBlock);
            	decl.add(new Procedure(loc, new Attribute[0], nread, new String[0],
            			inRead, outRead, null, bread));
            }
        }
		return decl;
	}
	
	
	private Expression constructPointerComponentAddition(
			ILocation loc, Expression left, Expression right) {
		return m_ExpressionTranslation.constructArithmeticExpression(
				loc, 
				IASTBinaryExpression.op_plus, left, 
				m_ExpressionTranslation.getCTypeOfPointerComponents(), right, m_ExpressionTranslation.getCTypeOfPointerComponents());
	}
	
	private Expression constructPointerComponentLessEqual(
			ILocation loc, Expression left, Expression right) {
		return m_ExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, 
				left, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
				right, m_ExpressionTranslation.getCTypeOfPointerComponents());
	}
	
	

    /**
     * Generate <code>procedure ~free(~addr:$Pointer$) returns()</code>'s
     * declaration and implementation.
     * 
     * @param tuLoc
     *            the location for the new nodes.
     * @return declaration and implementation of procedure <code>~free</code>
     */
    private ArrayList<Declaration> declareFree(Dispatcher main, final ILocation tuLoc) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        // procedure ~free(~addr:$Pointer$) returns();
        // requires #valid[~addr!base];
        // ensures #valid = old(valid)[~addr!base := false];
        // modifies #valid;
        Expression nr0 = m_ExpressionTranslation.constructLiteralForIntegerType(
        		tuLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
        Expression bLFalse = new BooleanLiteral(tuLoc, false);
        Expression addr = new IdentifierExpression(tuLoc, ADDR);
        Expression valid = new IdentifierExpression(tuLoc, SFO.VALID);
        Expression addrOffset = new StructAccessExpression(tuLoc, addr,
                SFO.POINTER_OFFSET);
        Expression addrBase = new StructAccessExpression(tuLoc, addr,
                SFO.POINTER_BASE);
        Expression[] idcFree = new Expression[] { addrBase };
        
        ArrayList<Specification> specFree = new ArrayList<Specification>();

        /* 
         * creating the specification according to C99:7.20.3.2-2:
         * The free function causes the space pointed to by ptr to be deallocated, that is, made
         * available for further allocation. If ptr is a null pointer, no action occurs. Otherwise, if
         * the argument does not match a pointer earlier returned by the calloc, malloc, or
         * realloc function, or if the space has been deallocated by a call to free or realloc,
         * the behavior is undefined.
         */
        Check check = new Check(Spec.MEMORY_FREE);
        boolean free = !m_CheckFreeValid;
        RequiresSpecification offsetZero = new RequiresSpecification(
        		tuLoc, free, ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, 
        				addrOffset, nr0));
        check.addToNodeAnnot(offsetZero);
        specFree.add(offsetZero);

        // ~addr!base == 0
        Expression isNullPtr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, addrBase, new IntegerLiteral(tuLoc, "0"));

        //requires ~addr!base == 0 || #valid[~addr!base];
        RequiresSpecification baseValid = new RequiresSpecification(tuLoc, free,
        		ExpressionFactory.newBinaryExpression(tuLoc, Operator.LOGICOR,
        				isNullPtr,
        				new ArrayAccessExpression(tuLoc, valid, idcFree)));

        check.addToNodeAnnot(baseValid);
        specFree.add(baseValid);

        //ensures (if ~addr!base == 0 then #valid == old(#valid)[~addr!base := false] else #valid == old(#valid))
        Expression updateValidArray = 
        		ExpressionFactory.newIfThenElseExpression(tuLoc, isNullPtr, 
        				ExpressionFactory.newBinaryExpression(
        						tuLoc, Operator.COMPEQ, valid,
        						ExpressionFactory.newUnaryExpression(
        								tuLoc, UnaryExpression.Operator.OLD, valid)),
        				ExpressionFactory.newBinaryExpression(
        						tuLoc, Operator.COMPEQ, valid,
        						new ArrayStoreExpression(tuLoc, ExpressionFactory.newUnaryExpression(
        								tuLoc, UnaryExpression.Operator.OLD, valid),
        								idcFree, bLFalse))
        				);

        specFree.add(new EnsuresSpecification(tuLoc, free, updateValidArray));
        specFree.add(new ModifiesSpecification(tuLoc, false,
        		new VariableLHS[] { new VariableLHS(tuLoc, SFO.VALID) }));
        
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.FREE,
        		new String[0], new VarList[] { new VarList(tuLoc,
        				new String[] { ADDR }, main.typeHandler.constructPointerType(tuLoc)) }, new VarList[0],
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
        					new String[] { ADDR }, main.typeHandler.constructPointerType(tuLoc)) }, new VarList[0],
        					null, bodyFree));
        }
        return decl;
    }

    /**
     * Generate
     * <code>procedure ~malloc(~size:int) returns (#res:$Pointer$);</code>'s
     * declaration and implementation.
     * @param typeHandler 
     * 
     * @param tuLoc
     *            the location for the new nodes.
     * @return declaration and implementation of procedure <code>~malloc</code>
     */
    private ArrayList<Declaration> declareMalloc(ITypeHandler typeHandler, final ILocation tuLoc) {
        ASTType intType = typeHandler.ctype2asttype(tuLoc, m_ExpressionTranslation.getCTypeOfPointerComponents());
        Expression nr0 = m_ExpressionTranslation.constructLiteralForIntegerType(
        		tuLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
        Expression bLFalse = new BooleanLiteral(tuLoc, false);
        Expression addr = new IdentifierExpression(tuLoc, ADDR);
        Expression valid = new IdentifierExpression(tuLoc, SFO.VALID);
        Expression addrOffset = new StructAccessExpression(tuLoc, addr,
                SFO.POINTER_OFFSET);
        Expression addrBase = new StructAccessExpression(tuLoc, addr,
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
        Expression res = new IdentifierExpression(tuLoc, SFO.RES);
        Expression length = new IdentifierExpression(tuLoc, SFO.LENGTH);
        Expression[] idcMalloc = new Expression[] { new StructAccessExpression(
                tuLoc, res, SFO.POINTER_BASE) };
        Expression bLTrue = new BooleanLiteral(tuLoc, true);
        IdentifierExpression size = new IdentifierExpression(tuLoc, SIZE);
        List<Specification> specMalloc = new ArrayList<Specification>();
        if (m_CheckMallocNonNegative) {
        	RequiresSpecification nonNegative = new RequiresSpecification(tuLoc,
        			false, ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPGEQ, size, nr0));
        	nonNegative.getPayload().getAnnotations().put(
        		Check.getIdentifier(), new Check(Check.Spec.MALLOC_NONNEGATIVE));
        	specMalloc.add(nonNegative);
        }
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
                        new ArrayAccessExpression(tuLoc, ExpressionFactory.newUnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc), bLFalse)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, valid,
                        new ArrayStoreExpression(tuLoc, ExpressionFactory.newUnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc, bLTrue))));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
                        new StructAccessExpression(tuLoc, res,
                                SFO.POINTER_OFFSET), nr0)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ,
                        new StructAccessExpression(tuLoc, res,
                                SFO.POINTER_BASE), nr0)));
        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, length,
                        new ArrayStoreExpression(tuLoc, ExpressionFactory.newUnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, length),
                                idcMalloc, size))));
        specMalloc.add(new ModifiesSpecification(tuLoc, false, new VariableLHS[] {
                new VariableLHS(tuLoc, SFO.VALID), 
                new VariableLHS(tuLoc, SFO.LENGTH) }));
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.MALLOC,
                new String[0], new VarList[] { new VarList(tuLoc,
                        new String[] { SIZE }, intType) },
                new VarList[] { new VarList(tuLoc, new String[] { SFO.RES },
                		typeHandler.constructPointerType(tuLoc)) }, specMalloc.toArray(new Specification[0]), null));
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
        					new String[] { ADDR }, typeHandler.constructPointerType(tuLoc)) }) };
        	Statement[] block = new Statement[6];
        	block[0] = new AssumeStatement(tuLoc, ExpressionFactory.newBinaryExpression(tuLoc,
        			Operator.COMPEQ, addrOffset, nr0));
        	block[1] = new AssumeStatement(tuLoc, ExpressionFactory.newBinaryExpression(tuLoc,
        			Operator.COMPNEQ, addrBase, nr0));
        	block[2] = new AssumeStatement(tuLoc, ExpressionFactory.newUnaryExpression(tuLoc,
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
        			new LeftHandSide[] { new VariableLHS(tuLoc, SFO.RES) },
        			new Expression[] { addr });
        	Body bodyMalloc = new Body(tuLoc, localVars, block);
        	decl.add(new Procedure(tuLoc, new Attribute[0], SFO.MALLOC,
        			new String[0], new VarList[] { new VarList(tuLoc,
        					new String[] { SIZE }, intType) },
        					new VarList[] { new VarList(tuLoc, new String[] { SFO.RES },
        							typeHandler.constructPointerType(tuLoc)) }, null, bodyMalloc));
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
    public CallStatement getFreeCall(Dispatcher main, FunctionHandler fh,
            LRValue lrVal, ILocation loc) {
    	assert lrVal instanceof RValue || lrVal instanceof LocalLValue;
//    	assert lrVal.cType instanceof CPointer;//TODO -> must be a pointer or onHeap -- add a complicated assertion or let it be??
    	
        // Further checks are done in the precondition of ~free()!
        // ~free(E);
        CallStatement freeCall = new CallStatement(loc, false, new VariableLHS[0], SFO.FREE,
                new Expression[] { lrVal.getValue() });
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
        return freeCall;
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
    public ExpressionResult getMallocCall(Dispatcher main, FunctionHandler fh,
            Expression size, ILocation loc) {
    	String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MALLOC);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, main.typeHandler.constructPointerType(loc), loc);
        
        LocalLValue llVal = new LocalLValue(new VariableLHS(loc, tmpId), new CPointer(new CPrimitive(PRIMITIVE.VOID)));
        ExpressionResult mallocRex = new ExpressionResult(llVal);
        
        mallocRex.stmt.add(getMallocCall(main, fh, size, llVal, loc));
        mallocRex.auxVars.put(tVarDecl, loc);
        mallocRex.decl.add(tVarDecl);
        
		assert (CHandler.isAuxVarMapcomplete(main, mallocRex.decl, mallocRex.auxVars));
		return mallocRex;
    }

    public CallStatement getMallocCall(Dispatcher main,	FunctionHandler fh, 
			LocalLValue resultPointer, ILocation loc) {
    	return getMallocCall(main, fh, calculateSizeOf(loc, resultPointer.getCType()), resultPointer, loc);
    }

    private CallStatement getMallocCall(Dispatcher main,	FunctionHandler fh, Expression size,
			LocalLValue resultPointer, ILocation loc) {
        Expression[] args = new Expression[] { size };
        
        CallStatement mallocCall = new CallStatement(loc, false, new VariableLHS[] { (VariableLHS) resultPointer.getLHS() },
                SFO.MALLOC, args);
        
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
        return mallocCall;
    }
    
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
    // 2015-10
    public ExpressionResult getReadCall(Dispatcher main, Expression address,
    		CType resultType) {
    	ILocation loc = (ILocation) address.getLocation();
    	if (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
    			&& (resultType.getUnderlyingType() instanceof CPrimitive)) {
    		CPrimitive cPrimitive = (CPrimitive) resultType.getUnderlyingType();
    		if (main.getTypeSizes().getSize(cPrimitive.getType()) > 
    				main.getTypeSizes().getSize(PRIMITIVE.INT)) {
    			throw new UnsupportedSyntaxException(loc, 
    					"cannot read " + cPrimitive + " from heap"); 
    		}
    	}
		boolean bitvectorConversionNeeded = (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
    			&& (resultType.getUnderlyingType() instanceof CPrimitive)
    			&& main.getTypeSizes().getSize(((CPrimitive) resultType.getUnderlyingType()).getType()) < 
				main.getTypeSizes().getSize(PRIMITIVE.INT));
    	
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
        
        
        ASTType heapType = getHeapTypeOfLRVal(main, loc, resultType);
        
        final String heapTypeName = getHeapTypeName(resultType);
        
        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD);
        final ASTType tmpAstType;
        if (bitvectorConversionNeeded) {
        	tmpAstType = main.typeHandler.ctype2asttype(loc, m_ExpressionTranslation.getCTypeOfIntArray());
        } else {
        	tmpAstType = heapType;
        }
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, tmpAstType, loc);
        auxVars.put(tVarDecl, loc);
        decl.add(tVarDecl);
        VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, tmpId) };
        CallStatement call = new CallStatement(loc, false, lhs, "read~" + heapTypeName,//heapType.toString(),
                new Expression[] { address, this.calculateSizeOf(loc, resultType) });
        for (Overapprox overapprItem : overappr) {
            call.getPayload().getAnnotations().put(Overapprox.getIdentifier(),
                    overapprItem);
        }
        stmt.add(call);
		assert (CHandler.isAuxVarMapcomplete(main, decl, auxVars));
		
		ExpressionResult result; 
		if (bitvectorConversionNeeded) {
			result = new ExpressionResult(stmt, 
	        		new RValue(new IdentifierExpression(loc, tmpId), m_ExpressionTranslation.getCTypeOfIntArray()),
	        		decl, auxVars, overappr);
			m_ExpressionTranslation.convertIntToInt(loc, result, (CPrimitive) resultType.getUnderlyingType());
	        String bvtmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD);
	        VariableDeclaration bvtVarDecl = SFO.getTempVarVariableDeclaration(bvtmpId, heapType, loc);
	        auxVars.put(bvtVarDecl, loc);
	        decl.add(bvtVarDecl);
	        VariableLHS[] bvlhs = new VariableLHS[] { new VariableLHS(loc, bvtmpId) };
	        AssignmentStatement as = new AssignmentStatement(loc, bvlhs, new Expression[] { result.lrVal.getValue() });
	        stmt.add(as);
	        result.lrVal = new RValue(new IdentifierExpression(loc, bvtmpId), resultType);
		} else {
			 result = new ExpressionResult(stmt, 
		        		new RValue(new IdentifierExpression(loc, tmpId), resultType),
		        		decl, auxVars, overappr);
		}
        return result;
    }
    
    
    private String getHeapTypeName(CType cType) {
    	CType underlyingType = cType.getUnderlyingType();
    	if (underlyingType instanceof CPrimitive) {
    		CPrimitive cPrimitive = (CPrimitive) underlyingType;
    		if (cPrimitive.isIntegerType()) {
    			return SFO.INT;
    		} else if (cPrimitive.isFloatingType()) {
    			throw new UnsupportedOperationException("I don't know the right String");
    		} else {
    			throw new UnsupportedOperationException("unknown type " + underlyingType);
    		}
    	} else if (underlyingType instanceof CEnum) {
    		return SFO.INT;
    	} else if (underlyingType instanceof CPointer) {
    		return SFO.POINTER;
    	} else {
    		throw new AssertionError("unable to write " + cType + " to heap");
    	}
    }
    
    ASTType getHeapTypeOfLRVal(Dispatcher main, ILocation loc, CType ct) {
    	
    	CType ut = ct;
    	if (ut instanceof CNamed)
    		ut = ((CNamed) ut).getUnderlyingType();
    	
    	if (ut instanceof CPrimitive) {
			CPrimitive cp = (CPrimitive) ut;
			switch (cp.getGeneralType()) {
			case INTTYPE:
				isIntArrayRequiredInMM = true;
				break;
			case FLOATTYPE:
				isFloatArrayRequiredInMM = true;
				break;
			default:
				throw new UnsupportedSyntaxException(null, "unsupported cType " + ct);
			}
			return main.typeHandler.ctype2asttype(loc, ct);
		} else if (ut instanceof CPointer) {
			isPointerArrayRequiredInMM = true;
			return main.typeHandler.constructPointerType(loc);
		} else if (ut instanceof CNamed) {
			assert false : "This should not be the case as we took the underlying type.";
			throw new UnsupportedSyntaxException(null, "non-heap type?: " + ct);
		} else if (ut instanceof CArray) {
			// we assume it is an Array on Heap
//			assert main.cHandler.isHeapVar(((IdentifierExpression) lrVal.getValue()).getIdentifier());
			//but it may not only be on heap, because it is addressoffed, but also because it is inside
			// a struct that is addressoffed..
			isPointerArrayRequiredInMM = true;
			return main.typeHandler.constructPointerType(loc);
		} else if (ut instanceof CEnum) { 
			//enum is treated like an int
			isIntArrayRequiredInMM = true;
			return main.typeHandler.ctype2asttype(loc, new CPrimitive(PRIMITIVE.INT));
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
    public ArrayList<Statement> getWriteCall(Dispatcher main, ILocation loc, HeapLValue hlv, 
    		Expression value, CType valueType) {
    	if (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
    			&& (valueType.getUnderlyingType() instanceof CPrimitive)) {
    		CPrimitive cPrimitive = (CPrimitive) valueType.getUnderlyingType();
    		if (main.getTypeSizes().getSize(cPrimitive.getType()) > 
    				main.getTypeSizes().getSize(PRIMITIVE.INT)) {
    			throw new UnsupportedSyntaxException(loc, 
    					"cannot write " + cPrimitive + " to heap"); 
    		}
    	}
		boolean bitvectorConversionNeeded = (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
    			&& (valueType.getUnderlyingType() instanceof CPrimitive)
    			&& main.getTypeSizes().getSize(((CPrimitive) valueType.getUnderlyingType()).getType()) < 
				main.getTypeSizes().getSize(PRIMITIVE.INT));
		if (bitvectorConversionNeeded) {
			RValue tmpworkaroundrvalue = new RValue(value, valueType.getUnderlyingType(), false, false);
			ExpressionResult tmpworkaround = new ExpressionResult(tmpworkaroundrvalue);
			m_ExpressionTranslation.convertIntToInt(loc, tmpworkaround, new CPrimitive(PRIMITIVE.INT));
			value = tmpworkaround.lrVal.getValue();
			valueType = tmpworkaround.lrVal.getCType();
		}
		
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        
        if (valueType instanceof CNamed)
        	valueType = ((CNamed) valueType).getUnderlyingType();
        
        if (valueType instanceof CPrimitive) {
        	switch (((CPrimitive) valueType).getGeneralType()) {
        	case INTTYPE:
        		isIntArrayRequiredInMM = true;
        		m_functionHandler.getModifiedGlobals().
        			get(m_functionHandler.getCurrentProcedureID()).add(SFO.MEMORY_INT);
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.INT,
        				new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType())}));
        		break;
        	case FLOATTYPE:
        		isFloatArrayRequiredInMM = true;
        		m_functionHandler.getModifiedGlobals().
        			get(m_functionHandler.getCurrentProcedureID()).add(SFO.MEMORY_REAL);
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.REAL,
        				new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType()) }));
        		break;	
        	default:
        		throw new UnsupportedSyntaxException(loc, "we don't recognize this type");
        	}
        } else if (valueType instanceof CEnum) {
        	//treat like INT
        	isIntArrayRequiredInMM = true;
        	m_functionHandler.getModifiedGlobals().
        	get(m_functionHandler.getCurrentProcedureID()).add(SFO.MEMORY_INT);
        	stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.INT,
        			new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType())}));
        } else if (valueType instanceof CPointer) {
        	isPointerArrayRequiredInMM = true;
        	m_functionHandler.getModifiedGlobals().
        			get(m_functionHandler.getCurrentProcedureID()).add(SFO.MEMORY_POINTER);
        	stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.POINTER,
        			new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType()) }));
        } else if (valueType instanceof CStruct) {
        	CStruct rStructType = (CStruct) valueType;
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
        				value, fieldId);
        		Expression fieldOffset = m_TypeSizeAndOffsetComputer.constructOffsetForField(loc, rStructType, fieldId);
        		Expression newOffset = m_ExpressionTranslation.constructArithmeticExpression(
        				loc, IASTBinaryExpression.op_plus, 
        				newStartAddressOffset, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
        				fieldOffset, m_ExpressionTranslation.getCTypeOfPointerComponents());
        		HeapLValue fieldHlv = new HeapLValue(
        				constructPointerFromBaseAndOffset(newStartAddressBase,
        				newOffset, loc), fieldType);
        		stmt.addAll(getWriteCall(main, loc, fieldHlv, sae, fieldType));
        	}
        	
        } else if (valueType instanceof CArray) {
//        	stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { 
//        			new VariableLHS(loc, ((IdentifierExpression )hlv.getAddress()).getIdentifier()) }, 
//        			new Expression[] { rval.getValue()}) );
        	isPointerArrayRequiredInMM = true;
        	m_functionHandler.getModifiedGlobals().
        			get(m_functionHandler.getCurrentProcedureID()).add(SFO.MEMORY_POINTER);
        	
        	CArray arrayType = (CArray) valueType;
        	Expression arrayStartAddress = hlv.getAddress();
        	Expression newStartAddressBase = null;
        	Expression newStartAddressOffset = null;
        	if (arrayStartAddress instanceof StructConstructor) {
        		newStartAddressBase = ((StructConstructor) arrayStartAddress).getFieldValues()[0];
        		newStartAddressOffset = ((StructConstructor) arrayStartAddress).getFieldValues()[1];
        	} else {
        		newStartAddressBase = MemoryHandler.getPointerBaseAddress(arrayStartAddress, loc);
        		newStartAddressOffset = MemoryHandler.getPointerOffset(arrayStartAddress, loc);
        	}

        	Expression valueTypeSize = calculateSizeOf(loc, arrayType.getValueType());

        	Expression arrayEntryAddressOffset = newStartAddressOffset;

        	//can we assume here, that we have a boogie array, right??
        	if (arrayType.getDimensions().length == 1) {
        			BigInteger dimBigInteger = m_ExpressionTranslation.extractIntegerValue(arrayType.getDimensions()[0]);
        			if (dimBigInteger == null) {
        				throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
        			}
					int dim = dimBigInteger.intValue();

//					Expression readArrayEntryAddressOffset = arrayType.isOnHeap() ? getPointerOffset(rval.getValue(), loc) : null;

					for (int pos = 0; pos < dim; pos++) {
						RValue arrayAccRVal;
//						if (arrayType.isOnHeap()) {
//							arrayAccRVal = new RValue(
//									constructPointerFromBaseAndOffset(
//											getPointerBaseAddress(rval.getValue(), loc),
//											readArrayEntryAddressOffset, loc),
//											arrayType.getValueType());
//							readArrayEntryAddressOffset = CHandler.createArithmeticExpression(IASTBinaryExpression.op_plus, 
//								readArrayEntryAddressOffset, valueTypeSize, loc);
//						} else {
							Expression position = m_ExpressionTranslation.constructLiteralForIntegerType(
									loc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(pos));
							arrayAccRVal = new RValue(
									new ArrayAccessExpression(loc, 
											value, 
											new Expression[] { position }), arrayType.getValueType());
//						}
						stmt.addAll(getWriteCall(main, loc, 
								new HeapLValue(constructPointerFromBaseAndOffset(newStartAddressBase, arrayEntryAddressOffset, loc), arrayType.getValueType()), 
								arrayAccRVal.getValue(), arrayAccRVal.getCType()));
						//TODO 2015-10-11 Matthias: Why is there an addition of value Type size
						// and no multiplication? Check this more carefully.
						arrayEntryAddressOffset = m_ExpressionTranslation.constructArithmeticExpression(
		        				loc, IASTBinaryExpression.op_plus, 
		        				arrayEntryAddressOffset, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
		        				valueTypeSize, m_ExpressionTranslation.getCTypeOfPointerComponents());
					}
        	} else {
        		throw new UnsupportedSyntaxException(loc, "we need to generalize this to nested and/or variable length arrays");
        	}
        	
//        	stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.POINTER,
//        			new Expression[] { rval.getValue(), hlv.getAddress(), this.calculateSizeOf(hlv.cType, loc) }));
        } else
        	throw new UnsupportedSyntaxException(loc, "we don't recognize this type");
		
        return stmt;
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
		return new StructAccessExpression(loc, pointer, "base");
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
		return new StructAccessExpression(loc, pointer, "offset");
	}
	
	public static StructConstructor constructPointerFromBaseAndOffset(Expression base, Expression offset, ILocation loc) {
		return new StructConstructor(loc, new String[]{"base", "offset"}, new Expression[]{base, offset}); 
	}
	
	/**
	 * Takes a loop or function body and inserts mallocs and frees for all the identifiers in this.mallocedAuxPointers
	 */
	public ArrayList<Statement> insertMallocs(Dispatcher main, ArrayList<Statement> block) {
		ArrayList<Statement> mallocs = new ArrayList<Statement>();
		for (LocalLValueILocationPair llvp : this.variablesToBeMalloced.currentScopeKeys()) 
			mallocs.add(this.getMallocCall(main, m_functionHandler, 
					llvp.llv, llvp.loc));
		ArrayList<Statement> frees = new ArrayList<Statement>();
		for (LocalLValueILocationPair llvp : this.variablesToBeFreed.currentScopeKeys()) {  //frees are inserted in handleReturnStm
			frees.add(this.getFreeCall(main, m_functionHandler, llvp.llv, llvp.loc));
			frees.add(new HavocStatement(llvp.loc, new VariableLHS[] { (VariableLHS) llvp.llv.getLHS() }));
		}
		ArrayList<Statement> newBlockAL = new ArrayList<Statement>();
		newBlockAL.addAll(mallocs);
		newBlockAL.addAll(block);
		newBlockAL.addAll(frees);
		return newBlockAL;
	}
	
	public void addVariableToBeFreed(Dispatcher main, LocalLValueILocationPair llvp) {
		this.variablesToBeFreed.put(llvp, variablesToBeFreed.getActiveScopeNum());
	}
	
	public LinkedScopedHashMap<LocalLValueILocationPair, Integer> getVariablesToBeMalloced() {
		return variablesToBeMalloced;
	}
	public LinkedScopedHashMap<LocalLValueILocationPair, Integer> getVariablesToBeFreed() {
		return variablesToBeFreed;
	}

	public POINTER_CHECKMODE getPointerSubtractionAndComparisonValidityCheckMode() {
		return m_checkPointerSubtractionAndComparisonValidity;
	}
	
	public Expression constructNullPointer(ILocation loc) {
//		return new IdentifierExpression(loc, SFO.NULL);
		return constructPointerForIntegerValues(loc, BigInteger.ZERO, BigInteger.ZERO);
	}
	
	public Expression constructPointerForIntegerValues(ILocation loc, BigInteger baseValue, BigInteger offsetValue) {
		Expression base = m_ExpressionTranslation.constructLiteralForIntegerType(loc, 
				m_ExpressionTranslation.getCTypeOfPointerComponents(), baseValue);
		Expression offset = m_ExpressionTranslation.constructLiteralForIntegerType(loc, 
				m_ExpressionTranslation.getCTypeOfPointerComponents(), offsetValue);
		return constructPointerFromBaseAndOffset(base, offset, loc); 
	}

	


	public TypeSizeAndOffsetComputer getTypeSizeAndOffsetComputer() {
		return m_TypeSizeAndOffsetComputer;
	}
	

}
