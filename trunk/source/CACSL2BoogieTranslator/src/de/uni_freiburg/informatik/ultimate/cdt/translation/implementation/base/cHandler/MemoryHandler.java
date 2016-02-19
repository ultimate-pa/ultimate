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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
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
	private final POINTER_CHECKMODE m_PointerTargetFullyAllocated;
	private final boolean m_CheckFreeValid;
	private final boolean m_CheckMallocNonNegative;
	
	//needed for adding modifies clauses
	private final FunctionHandler m_FunctionHandler;
	private final ITypeHandler m_TypeHandler;

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

	private boolean m_declareMemCpy = false;
	private boolean m_declareMemset = false;
	
	public void setDeclareMemCpy() {
		m_declareMemCpy = true;
	}

	public void setDeclareMemset() {
		m_declareMemset = true;
	}
	
	private final AExpressionTranslation m_ExpressionTranslation;
	
	private final TypeSizeAndOffsetComputer m_TypeSizeAndOffsetComputer;
	private final RequiredMemoryModelFeatures m_RequiredMemoryModelFeatures;
	private final MemoryModel m_MemoryModel;
	
	
	/**
     * Constructor.
	 * @param typeHandler 
     * @param checkPointerValidity 
	 * @param typeSizeComputer 
     */
    public MemoryHandler(ITypeHandler typeHandler, FunctionHandler functionHandler, boolean checkPointerValidity, 
    		TypeSizeAndOffsetComputer typeSizeComputer, TypeSizes typeSizes, AExpressionTranslation expressionTranslation) {
    	m_TypeHandler = typeHandler;
    	m_FunctionHandler = functionHandler;
    	m_ExpressionTranslation = expressionTranslation;
    	m_RequiredMemoryModelFeatures = new RequiredMemoryModelFeatures();
    	m_MemoryModel = new MemoryModel(0, typeSizes, typeHandler, expressionTranslation);
		this.variablesToBeMalloced = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		this.variablesToBeFreed = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		//read preferences from settings
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		
		m_PointerBaseValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, POINTER_CHECKMODE.class);
    	m_PointerTargetFullyAllocated = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, POINTER_CHECKMODE.class);
    	m_CheckFreeValid = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		m_CheckMallocNonNegative = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MallocNonNegative);
    	m_checkPointerSubtractionAndComparisonValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY, POINTER_CHECKMODE.class);
		
		m_TypeSizeAndOffsetComputer = typeSizeComputer;
    }
    
    public class RequiredMemoryModelFeatures {
    	private final Set<PRIMITIVE> m_DataOnHeapRequired = new HashSet<>();
    	private boolean m_PointerOnHeapRequired;
    	
    	public void reportPointerOnHeapRequired() {
    		m_PointerOnHeapRequired = true;
    	}
    	
    	public void reportDataOnHeapRequired(PRIMITIVE primitive) {
    		m_DataOnHeapRequired.add(primitive);
    	}
    	
    	public boolean isPointerOnHeapRequired() {
    		return m_PointerOnHeapRequired;
    	}

		public Set<PRIMITIVE> getDataOnHeapRequired() {
			return m_DataOnHeapRequired;
		}
    	
    	
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
       

        decl.add(constructNullPointerConstant());
        decl.add(constructValidArrayDeclaration());
        decl.add(constuctLengthArrayDeclaration());
        
        // add memory arrays and access procedures
        ArrayList<HeapDataArray> heapDataArrays = m_MemoryModel.getDataHeapArrays(m_RequiredMemoryModelFeatures);
        
        decl.addAll(declareSomeMemoryArrays(tuLoc, heapDataArrays));

        decl.addAll(declareFree(main, tuLoc));
        decl.addAll(declareDeallocation(main, tuLoc));
        decl.addAll(declareMalloc(main.typeHandler, tuLoc));

        if (m_declareMemCpy) {
        	decl.addAll(declareMemCpy(main, heapDataArrays));
        }
        if (m_declareMemset) {
        	decl.addAll(declareMemset(main, heapDataArrays));
        }

        return decl;
    }

	private VariableDeclaration constuctLengthArrayDeclaration() {
		// var #length : [int]int;
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
        ASTType pointerComponentType = m_TypeHandler.ctype2asttype(ignoreLoc, 
        		m_ExpressionTranslation.getCTypeOfPointerComponents());
        ASTType lengthType = new ArrayType(ignoreLoc, new String[0],
                new ASTType[] { pointerComponentType }, pointerComponentType);
        VarList vlL = new VarList(ignoreLoc, new String[] { SFO.LENGTH },
                lengthType);
        return new VariableDeclaration(ignoreLoc, new Attribute[0],
                new VarList[] { vlL });
	}

	private VariableDeclaration constructValidArrayDeclaration() {
        // var #valid : [int]bool;
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
        ASTType pointerComponentType = m_TypeHandler.ctype2asttype(ignoreLoc, 
        		m_ExpressionTranslation.getCTypeOfPointerComponents());
        ASTType validType = new ArrayType(ignoreLoc, new String[0],
                new ASTType[] { pointerComponentType }, new PrimitiveType(ignoreLoc, "bool"));
        VarList vlV = new VarList(ignoreLoc, new String[] { SFO.VALID }, validType);
        return new VariableDeclaration(ignoreLoc, new Attribute[0],
                new VarList[] { vlV });
	}

	private VariableDeclaration constructNullPointerConstant() {
		// NULL Pointer
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
        VariableDeclaration result = new VariableDeclaration(ignoreLoc, new Attribute[0],
                new VarList[] { new VarList(ignoreLoc, new String[] { SFO.NULL },
                		m_TypeHandler.constructPointerType(ignoreLoc)) });
		return result;
	}

    /**
     * Adds our implementation of the memcpy procedure to the boogie code.
     */
    private List<Declaration> declareMemCpy(Dispatcher main,
    		List<HeapDataArray> heapDataArrays) {
    	ArrayList<Declaration> memCpyDecl = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	VarList inPDest = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_DEST }, main.typeHandler.constructPointerType(ignoreLoc));
    	VarList inPSrc = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SRC }, main.typeHandler.constructPointerType(ignoreLoc));
    	VarList	inPSize = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SIZE }, new PrimitiveType(ignoreLoc, SFO.INT));
    	VarList[] inParams = new VarList[] { inPDest, inPSrc, inPSize };
    	
    	VarList[] outParams = new VarList[] { new VarList(ignoreLoc, new String[] { SFO.RES }, main.typeHandler.constructPointerType(ignoreLoc)) };

   			
    	ArrayList<VariableDeclaration> decl = new ArrayList<>();
    	ArrayList<Statement> stmt = new ArrayList<>();
    	
    	CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
    	String loopCtr = main.nameHandler.getTempVarUID(SFO.AUXVAR.LOOPCTR, intType);
    	ASTType astType = new PrimitiveType(ignoreLoc, SFO.INT); //TODO: translate via type handler
		VarList lcvl = new VarList(ignoreLoc, new String[] { loopCtr }, astType);
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
		for (HeapDataArray hda : heapDataArrays) {
			String memArrayName = hda.getVariableName();

			ArrayAccessExpression srcAcc = new ArrayAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, memArrayName), new Expression[] { currentSrc });
			ArrayLHS destAcc = new ArrayLHS(ignoreLoc, new VariableLHS(ignoreLoc, memArrayName), new Expression[] { currentDest });
			bodyStmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { destAcc }, new Expression[] { srcAcc }));

			modifiesLHSs.add(new VariableLHS(ignoreLoc, memArrayName));

			if (m_FunctionHandler.getModifiedGlobals().get(SFO.MEMCPY) == null){
				m_FunctionHandler.getModifiedGlobals().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			if (m_FunctionHandler.getCallGraph().get(SFO.MEMCPY) == null) {
				m_FunctionHandler.getCallGraph().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			m_FunctionHandler.getModifiedGlobals().get(SFO.MEMCPY).add(memArrayName);
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
	
		
        Expression valid = getValidArray(ignoreLoc);	
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
				getLenthArray(ignoreLoc),
				new Expression[] { srcBase });
		Expression lengthDest = new ArrayAccessExpression(ignoreLoc,
				getLenthArray(ignoreLoc),
				new Expression[] { srcBase });

		if (m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSERTandASSUME 
				|| m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSUME) {
			// requires #sizeof~$Pointer$ + #ptr!offset <=
					// #length[#ptr!base];
        	RequiresSpecification specLengthSrc = null;
        	RequiresSpecification specLengthDest = null;
			if (m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
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
				assert m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSUME;
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
     * Returns a (Boogie) declaration and an implementation for the method
     * ULTIMATE.memset(startPointer : Pointer, noFields : int, sizeofFields : int, valueToBeWritten : int) returns ()
     * This method should set a continuous list of memory locations beginning at address
     * "startPointer" to the value "valueToBeWritten". The list of memory locations is given
     * by repeatedly adding "sizeOfField" to "startPointer" for "noFields" times.
     * 
     * This method is supposed to be called by our implementations for the C methods calloc and 
     * memset.
     * 
     * @param main
     * @param namesOfAllMemoryArrayTypes
     * @param astTypesOfAllMemoryArrayTypes
     * @return
     */
    private List<Declaration> declareMemset(Dispatcher main, 
    		List<HeapDataArray> heapDataArrays) {

    	List<Declaration> memsetDecls = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	List<Declaration> localDecls = new ArrayList<>();
    	List<Statement> statements = new ArrayList<>();

    	
    	//var ctr : int;
    	// ctr := 0;
    	// while (ctr < noFields) {
    	//   write~int(valueToBeWritten, { startPointer!Base, startPointer!Offset + (ctr * sizeOfFields) });
    	//   write~Pointer(valueToBeWritten, { startPointer!Base, startPointer!Offset + (ctr * sizeOfFields) });
    	//   ctr := ctr + 1;
    	// }
    	
    	String startPointerName = "startPointer";
		IdentifierExpression startPointer = new IdentifierExpression(ignoreLoc, startPointerName);
     	String valueName = "value";
		IdentifierExpression value = new IdentifierExpression(ignoreLoc, valueName);
      	String noFieldsName = "noFields";
		IdentifierExpression noFields = new IdentifierExpression(ignoreLoc, noFieldsName);
       	String sizeofFieldsName = "sizeofFields";
		IdentifierExpression sizeofFields = new IdentifierExpression(ignoreLoc, sizeofFieldsName);
    	

    	//var ctr : int;
    	String ctrName = "ctr";
    	VariableDeclaration ctrDec = new VariableDeclaration(
    			ignoreLoc, 
    			new Attribute[0], 
    			new VarList[] { new VarList(ignoreLoc, new String[] { ctrName }, new PrimitiveType(ignoreLoc, SFO.INT))});
    	localDecls.add(ctrDec);
    	
    	// ctr := 0;
        Expression nr0 = m_ExpressionTranslation.constructLiteralForIntegerType(
        		ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
    	AssignmentStatement ctrInit = new AssignmentStatement(ignoreLoc, 
    			new LeftHandSide[] { new VariableLHS(ignoreLoc, ctrName) }, 
    			new Expression[] { nr0 });
    	statements.add(ctrInit);
    	
    	
		List<Statement> whileBody = new ArrayList<>();

    	//{ startPointer!Base, startPointer!Offset + (ctr * sizeOfFields) }
		IdentifierExpression ctr = new IdentifierExpression(ignoreLoc, ctrName);
    	StructConstructor curAddr = constructPointerFromBaseAndOffset(
    			getPointerBaseAddress(startPointer, ignoreLoc),
    			ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.ARITHPLUS, 
    					getPointerOffset(startPointer, ignoreLoc),
    					ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.ARITHMUL, ctr, sizeofFields)),
    			ignoreLoc);

    	if (m_FunctionHandler.getModifiedGlobals().get(SFO.MEMSET) == null)
    		m_FunctionHandler.getModifiedGlobals().put(SFO.MEMSET, new LinkedHashSet<>());
    	if (m_FunctionHandler.getCallGraph().get(SFO.MEMSET) == null)
    		m_FunctionHandler.getCallGraph().put(SFO.MEMSET, new LinkedHashSet<String>());

    	//TODO: this is designed to work only for the memory arrays for int and pointer, if we want to support others, 
    	// like floats or so, we have to add a case here
    	//if (namesOfAllMemoryArrayTypes.contains(SFO.INT)) {
    	if (true) {
    		//   write~int(valueToBeWritten, { startPointer!Base, startPointer!Offset + (ctr * sizeOfFields) });

    		m_FunctionHandler.getModifiedGlobals().get(SFO.MEMSET).add(SFO.MEMORY_INT);

    		whileBody.add(new CallStatement(ignoreLoc, false, new VariableLHS[0], "write~" + SFO.INT,
    				new Expression[] { value, curAddr, sizeofFields}));	
    	}
    	if (true) {
//    	if (namesOfAllMemoryArrayTypes.contains(SFO.POINTER)) {
    		//   write~Pointer(valueToBeWritten, { startPointer!Base, startPointer!Offset + (ctr * sizeOfFields) });

//    		if (m_functionHandler.getModifiedGlobals().get(SFO.MEMSET) == null)
//    			m_functionHandler.getModifiedGlobals().put(SFO.MEMSET, new LinkedHashSet<>());
//    		if (m_functionHandler.getCallGraph().get(SFO.MEMSET) == null)
//    			m_functionHandler.getCallGraph().put(SFO.MEMSET, new LinkedHashSet<String>());
    		m_FunctionHandler.getModifiedGlobals().get(SFO.MEMSET).add(SFO.MEMORY_POINTER);

    		whileBody.add(new CallStatement(ignoreLoc, false, new VariableLHS[0], "write~" + SFO.POINTER,
    				new Expression[] { 
    						constructPointerFromBaseAndOffset(nr0, value, ignoreLoc), 
    						curAddr, 
    						sizeofFields}));	
    	}
    	
    	//   ctr := ctr + 1;
        Expression nr1 = m_ExpressionTranslation.constructLiteralForIntegerType(
        		ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
     	AssignmentStatement ctrInc = new AssignmentStatement(ignoreLoc, 
    			new LeftHandSide[] { new VariableLHS(ignoreLoc, ctrName) }, 
    			new Expression[] {ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.ARITHPLUS, 
    					ctr,
    					nr1) } );
     	whileBody.add(ctrInc);
    	
     	
     	// (ctr < noFields)
     	Expression condition = ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPLT, ctr, noFields);
     	
     	statements.add(new WhileStatement(ignoreLoc, 
     			condition, 
     			new LoopInvariantSpecification[0], 
     			whileBody.toArray(new Statement[whileBody.size()])));
     	
     	VarList[] inParams = new VarList[] { 
     							new VarList(ignoreLoc, 
     									new String[] { startPointerName }, 
     									new NamedType(ignoreLoc, SFO.POINTER, new ASTType[0])),
     							new VarList(ignoreLoc, 
     									new String[] { noFieldsName }, 
     									new PrimitiveType(ignoreLoc, SFO.INT)),
     							new VarList(ignoreLoc, 
     									new String[] { sizeofFieldsName }, 
     									new PrimitiveType(ignoreLoc, SFO.INT)),
     							new VarList(ignoreLoc, 
     									new String[] { valueName }, 
     									new PrimitiveType(ignoreLoc, SFO.INT)),
     							};
     	
     	
     	
		// tell function handler of this procedure
     	// to deal with modifies
		ArrayList<VariableLHS> modifiesLHSs = new ArrayList<>();
		for (HeapDataArray hda : heapDataArrays) {
			String memArrayName = hda.getVariableName();

			modifiesLHSs.add(new VariableLHS(ignoreLoc, memArrayName));

			if (!m_FunctionHandler.getModifiedGlobals().containsKey(SFO.MEMCPY)){
				m_FunctionHandler.getModifiedGlobals().put(SFO.MEMCPY, new LinkedHashSet<String>());
			}
			m_FunctionHandler.getModifiedGlobals().get(SFO.MEMCPY).add(memArrayName);
		}

		// make the specification
		ArrayList<Specification> specs = new ArrayList<>();
		
		CACSLLocation loc = LocationFactory.createIgnoreCLocation();
		Expression valid = new IdentifierExpression(loc, SFO.VALID);
        Expression addr = startPointer;
        Expression addrBase = new StructAccessExpression(loc, addr,
                SFO.POINTER_BASE);
        Expression[] idcWrite = new Expression[] { addrBase };
        Expression ptrOff = new StructAccessExpression(loc, startPointer,
        		SFO.POINTER_OFFSET);
        Expression ptrBase = new StructAccessExpression(loc, startPointer,
        		SFO.POINTER_BASE);
        Expression length = new ArrayAccessExpression(loc,
        		new IdentifierExpression(loc, SFO.LENGTH),
        		new Expression[] { ptrBase });
		
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
			specs.add(specValid);
		}


		if (m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSERTandASSUME 
				|| m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSUME) {
			// requires #sizeof~$Pointer$ + #ptr!offset <=
			// #length[#ptr!base];
			CPrimitive intCType = new CPrimitive(PRIMITIVE.INT);
			RequiresSpecification specValid;
			Expression sizeOfSetMemory = m_ExpressionTranslation.constructArithmeticIntegerExpression(loc, 
					IASTBinaryExpression.op_multiply, noFields, intCType, sizeofFields, intCType);
			
			if (m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
				specValid = new RequiresSpecification(loc, false,
						constructPointerComponentLessEqual(loc,
								constructPointerComponentAddition(loc,
										sizeOfSetMemory,
										ptrOff), length));
			} else {
				assert m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSUME;
				specValid = new RequiresSpecification(loc, true,
						constructPointerComponentLessEqual(loc,
								constructPointerComponentAddition(loc,
										sizeOfSetMemory,
										ptrOff), length));
			}
			Check check = new Check(Spec.MEMORY_DEREFERENCE);
			check.addToNodeAnnot(specValid);
			specs.add(specValid);
		}
		
		
		
		ModifiesSpecification modifies = new ModifiesSpecification(ignoreLoc, false, 
				 modifiesLHSs.toArray(new VariableLHS[modifiesLHSs.size()]));
		specs.add(modifies);
     	
		// make the actual declarations
     	memsetDecls.add(
     			new Procedure(ignoreLoc, 
     					new Attribute[0], 
     					SFO.MEMSET,
     					new String[0], 
     					inParams, 
     					new VarList[0], 
     					null,  //Spec
     					new Body(
     							ignoreLoc, 
     							localDecls.toArray(new VariableDeclaration[1]), 
     							statements.toArray(new Statement[statements.size()]))));
     	memsetDecls.add(
     			new Procedure(ignoreLoc, 
     					new Attribute[0], 
     					SFO.MEMSET,
     					new String[0], 
     					inParams, 
     					new VarList[0], 
     					specs.toArray(new Specification[specs.size()]),  //TODO: pointer safety specs?? like in memcpy??
     					null));
 
		return memsetDecls;
    }

    /**
     * Declares those of the memory arrays <code>#memory_int</code>,
     * <code>#memory_bool</code> (deprecated), <code>#memory_real</code> and
     * <code>#memory_$Pointer$</code>, that are listed in the arguments,
     * as well as read and write procedures for these arrays.
     * 
     * @param loc the location of the translation unit.
     * @return the declarations for the memory arrays as well as read and write
     *         procedures for these arrays.
     */
	private ArrayList<Declaration> declareSomeMemoryArrays(final ILocation loc, List<HeapDataArray> heapDataArrays) {
		ArrayList<Declaration> decl = new ArrayList<>();
        
		for (HeapDataArray heapDataArray : heapDataArrays) {

            decl.add(constructMemoryArrayDeclaration(loc, heapDataArray.getName(), heapDataArray.getASTType()));
            
            // create and add read and write procedure
           	decl.add(constructWriteProcedure(loc, heapDataArrays, heapDataArray));
            decl.add(constructReadProcedure(loc, heapDataArray));

        }
		return decl;
	}

	private VariableDeclaration constructMemoryArrayDeclaration(
			final ILocation loc, final String typeName, final ASTType astType) {
		final ASTType memoryArrayType = new ArrayType(loc, new String[0],
		        new ASTType[] { m_TypeHandler.constructPointerType(loc) }, astType);
		final VarList varList = new VarList(loc, new String[] { SFO.MEMORY + "_" 
		        + typeName }, memoryArrayType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { varList });
	}

	private Procedure constructWriteProcedure(final ILocation loc, 
			final List<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray) {
		String value = "#value";
		String inPtr = "#ptr";
		String writtenTypeSize = "#sizeOfWrittenType";
		String nwrite = "write~" + heapDataArray.getName();

		ASTType intType = m_TypeHandler.ctype2asttype(loc, m_ExpressionTranslation.getCTypeOfIntArray());
		VarList[] inWrite = new VarList[] {
				new VarList(loc, new String[] { value }, heapDataArray.getASTType()),
				new VarList(loc, new String[] { inPtr }, m_TypeHandler.constructPointerType(loc)),
				new VarList(loc, new String[] { writtenTypeSize }, intType) };
         
      
		// specification for memory writes
		ArrayList<Specification> swrite = new ArrayList<Specification>();

		addPointerBaseValidityCheck(loc, inPtr, swrite);

		Expression sizeWrite = new IdentifierExpression(loc, writtenTypeSize);
		checkPointerTargetFullyAllocated(loc, sizeWrite, inPtr, swrite);


		ModifiesSpecification mod = constructModifiesSpecification(loc, heapDataArrays, x -> x.getVariableName());
		swrite.add(mod);
		for (HeapDataArray other : heapDataArrays) {
			if (heapDataArray == other) {
				swrite.add(ensuresHeapArrayUpdate(loc, value, inPtr, other));
			} else {
				swrite.add(ensuresHeapArrayHardlyModified(loc, inPtr, other));
			}

		}
		Procedure result = new Procedure(loc, new Attribute[0], nwrite, new String[0],
				inWrite, new VarList[0], swrite.toArray(new Specification[swrite.size()]), null);
		return result;
	}

	private Procedure constructReadProcedure(final ILocation loc, HeapDataArray hda) {
		// specification for memory reads
		final String value = "#value";
		final String ptrId = "#ptr";
		final String nread = "read~" + hda.getName();
		final String readTypeSize = "#sizeOfReadType";
		ASTType intType = m_TypeHandler.ctype2asttype(loc, m_ExpressionTranslation.getCTypeOfIntArray());
		VarList[] inRead = new VarList[] { 
				new VarList(loc, new String[] { ptrId }, m_TypeHandler.constructPointerType(loc)),
				new VarList(loc, new String[] { readTypeSize }, intType) };
		VarList[] outRead = new VarList[] { new VarList(loc,
		        new String[] { value }, hda.getASTType()) };
		
		ArrayList<Specification> sread = new ArrayList<Specification>();
		
		addPointerBaseValidityCheck(loc, ptrId, sread);
		
		Expression sizeRead = new IdentifierExpression(loc, readTypeSize);
		checkPointerTargetFullyAllocated(loc, sizeRead, ptrId, sread);
		
		Expression arr = new IdentifierExpression(loc, hda.getVariableName());
		Expression ptrExpr = new IdentifierExpression(loc, ptrId);
		Expression[] index = new Expression[] { ptrExpr };
		Expression aae = new ArrayAccessExpression(loc, arr, index);
		Expression valueExpr = new IdentifierExpression(loc, value);
		Expression equality = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, valueExpr, aae);
		sread.add(new EnsuresSpecification(loc, false, equality));
		Procedure result = new Procedure(loc, new Attribute[0], nread, new String[0],
		        inRead, outRead, sread.toArray(new Specification[0]), null);
		return result;
	}

	// ensures #memory_X == old(#memory_X)[#ptr := #value];
	private EnsuresSpecification ensuresHeapArrayUpdate(final ILocation loc, 
			final String valueId, final String ptrId, final HeapDataArray hda) {
		final Expression valueExpr = new IdentifierExpression(loc, valueId);
        final Expression memArray = new IdentifierExpression(loc, hda.getVariableName());
        final Expression ptrExpr = new IdentifierExpression(loc, ptrId);
        final Expression[] index = new Expression[] { ptrExpr };
		return ensuresArrayUpdate(loc, valueExpr, index, memArray);
	}
	
	//#memory_$Pointer$ == old(#memory_X)[#ptr := #memory_X[#ptr]];
	private EnsuresSpecification ensuresHeapArrayHardlyModified(final ILocation loc, 
			final String ptrId, final HeapDataArray hda) {
        final Expression memArray = new IdentifierExpression(loc, hda.getVariableName());
        final Expression ptrExpr = new IdentifierExpression(loc, ptrId);
        final Expression[] index = new Expression[] { ptrExpr };
        final Expression aae = new ArrayAccessExpression(loc, memArray, index);
		return ensuresArrayUpdate(loc, aae, index, memArray);
	}
	
	
	
	private EnsuresSpecification ensuresArrayUpdate(final ILocation loc, 
			final Expression newValue, final Expression[] index, final Expression arrayExpr) {
		final Expression oldArray = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
        final ArrayStoreExpression ase = new ArrayStoreExpression(loc, oldArray, index, newValue);
        final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
		return new EnsuresSpecification(loc, false, eq);
	}

	/**
	 * 
	 * @param loc location of translation unit
	 * @param vars
	 * @return ModifiesSpecification which says that all variables of the
	 * set vars can be modified.
	 */
	private <T> ModifiesSpecification constructModifiesSpecification(
					final ILocation loc, final List<T> vars, final Function<T, String> varToString) {
		VariableLHS[] modifie = new VariableLHS[vars.size()];
		int i = 0;
		for (T variable : vars) {
			modifie[i] = new VariableLHS(loc, varToString.apply(variable));
			i++;
		}
		return new ModifiesSpecification(loc, false, modifie);
	}

	/**
	 * Add specification that target of pointer is fully allocated to the list 
	 * {@link specList}. The specification checks that the address of the
	 * pointer plus the size of the type that we read/write is smaller than or
	 * equal to the size of the allocated memory at the base address of the 
	 * pointer.
	 * In case m_PointerBaseValidity is ASSERTandASSUME, we add the requires
	 * specification 
	 * <code>requires #size + #ptr!offset <= #length[#ptr!base]</code>.
	 * In case m_PointerBaseValidity is ASSERTandASSUME, we add the <b>free</b>
	 * requires specification 
	 * <code>free requires #size + #ptr!offset <= #length[#ptr!base]</code>.
	 * In case m_PointerBaseValidity is IGNORE, we add nothing.
	 * @param loc location of translation unit
	 * @param size Expression that represents the size of the data type that we
	 *     read/write at the address of the pointer.
	 * @param ptrName name of pointer whose base address is checked
	 * @param specList list to which the specification is added
	 */
	private void checkPointerTargetFullyAllocated(final ILocation loc, 
			Expression size, String ptrName,
			ArrayList<Specification> specList) {
		if (m_PointerBaseValidity == POINTER_CHECKMODE.IGNORE) {
			// add nothing
			return;
		} else {
			final Expression ptrExpr = new IdentifierExpression(loc, ptrName);
			final Expression ptrBase = getPointerBaseAddress(ptrExpr, loc);
			final Expression aae = new ArrayAccessExpression(loc,
					getLenthArray(loc), new Expression[] { ptrBase });
			final Expression ptrOffset = getPointerOffset(ptrExpr, loc);
			final Expression sum = constructPointerComponentAddition(loc, size, ptrOffset);
			final Expression leq = constructPointerComponentLessEqual(loc, sum, aae);
			final boolean isFreeRequires;
			if (m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSERTandASSUME) {
				isFreeRequires = false;
			} else {
				assert m_PointerTargetFullyAllocated == POINTER_CHECKMODE.ASSUME;
				isFreeRequires = true;
			}
			final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, leq);
			Check check = new Check(Spec.MEMORY_DEREFERENCE);
			check.addToNodeAnnot(spec);
			specList.add(spec);
		}
	}

	/**
	 * Add specification that the pointer base address is valid to the list 
	 * {@link specList}.
	 * In case m_PointerBaseValidity is ASSERTandASSUME, we add the requires
	 * specification <code>requires #valid[#ptr!base]</code>.
	 * In case m_PointerBaseValidity is ASSERTandASSUME, we add the <b>free</b>
	 * requires specification <code>free requires #valid[#ptr!base]</code>.
	 * In case m_PointerBaseValidity is IGNORE, we add nothing.
	 * @param loc location of translation unit
	 * @param ptrName name of pointer whose base address is checked
	 * @param specList list to which the specification is added
	 */
	private void addPointerBaseValidityCheck(final ILocation loc, String ptrName,
			ArrayList<Specification> specList) {
		if (m_PointerBaseValidity == POINTER_CHECKMODE.IGNORE) {
			// add nothing
			return;
		} else {
			final Expression ptrExpr = new IdentifierExpression(loc, ptrName);
			final Expression ptrBase = getPointerBaseAddress(ptrExpr, loc);
			final ArrayAccessExpression aae = new ArrayAccessExpression(loc, 
					getValidArray(loc), new Expression[]{ ptrBase });
			final boolean isFreeRequires;
			if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME) {
		    	isFreeRequires = false;
			} else {
				assert m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME;
				isFreeRequires = true;
			}
			final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, aae);
			Check check = new Check(Spec.MEMORY_DEREFERENCE);
			check.addToNodeAnnot(spec);
			specList.add(spec);
		}
	}
	
	/**
	 * @param loc location of translation unit
	 * @return new IdentifierExpression that represents the <em>#length array</em>
	 */
	private Expression getLenthArray(final ILocation loc) {
		return new IdentifierExpression(loc, SFO.LENGTH);
	}

	/**
	 * @param loc location of translation unit
	 * @return new IdentifierExpression that represents the <em>#valid array</em>
	 */
	private Expression getValidArray(final ILocation loc) {
		return new IdentifierExpression(loc, SFO.VALID);
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
        Expression valid = getValidArray(tuLoc);
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
        Expression ptrBaseZero = m_ExpressionTranslation.constructLiteralForIntegerType(
        		tuLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
        Expression isNullPtr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, addrBase, ptrBaseZero);

        //requires ~addr!base == 0 || #valid[~addr!base];
        RequiresSpecification baseValid = new RequiresSpecification(tuLoc, free,
        		ExpressionFactory.newBinaryExpression(tuLoc, Operator.LOGICOR,
        				isNullPtr,
        				new ArrayAccessExpression(tuLoc, valid, idcFree)));

        check.addToNodeAnnot(baseValid);
        specFree.add(baseValid);

        //ensures (if ~addr!base == 0 then #valid == old(#valid) else #valid == old(#valid)[~addr!base := false])
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
     * Generate <code>procedure ULTIMATE.dealloc(~addr:$Pointer$) returns()</code>'s
     * declaration and implementation.
     * This procedure should be used for deallocations where do not want to
     * check if given memory area is valid (because we already know this)
     * which is the case, e.g., for arrays that we store on the heap or for
     * alloca.
     * 
     * @param tuLoc
     *            the location for the new nodes.
     * @return declaration and implementation of procedure <code>~free</code>
     */
    private ArrayList<Declaration> declareDeallocation(Dispatcher main, final ILocation tuLoc) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        // ensures #valid = old(valid)[~addr!base := false];
        Expression bLFalse = new BooleanLiteral(tuLoc, false);
        Expression addr = new IdentifierExpression(tuLoc, ADDR);
        Expression valid = getValidArray(tuLoc);
        Expression addrBase = new StructAccessExpression(tuLoc, addr,
                SFO.POINTER_BASE);
        Expression[] idcFree = new Expression[] { addrBase };
        
        ArrayList<Specification> specFree = new ArrayList<Specification>();

        Expression updateValidArray = 
        				ExpressionFactory.newBinaryExpression(
        						tuLoc, Operator.COMPEQ, valid,
        						new ArrayStoreExpression(tuLoc, ExpressionFactory.newUnaryExpression(
        								tuLoc, UnaryExpression.Operator.OLD, valid),
        								idcFree, bLFalse));

        specFree.add(new EnsuresSpecification(tuLoc, true, updateValidArray));
        specFree.add(new ModifiesSpecification(tuLoc, false,
        		new VariableLHS[] { new VariableLHS(tuLoc, SFO.VALID) }));
        
        decl.add(new Procedure(tuLoc, new Attribute[0], SFO.DEALLOC,
        		new String[0], new VarList[] { new VarList(tuLoc,
        				new String[] { ADDR }, main.typeHandler.constructPointerType(tuLoc)) }, new VarList[0],
        		specFree.toArray(new Specification[0]), null));

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
        Expression valid = getValidArray(tuLoc);
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
        Expression length = getLenthArray(tuLoc);
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
        specMalloc.add(ensuresArrayUpdate(tuLoc, bLTrue, idcMalloc, valid));
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
    
    /*
     * 2015-11-07 Matthias: This is copy&paste from getFreeCall
     */
    public CallStatement getDeallocCall(Dispatcher main, FunctionHandler fh,
            LRValue lrVal, ILocation loc) {
    	assert lrVal instanceof RValue || lrVal instanceof LocalLValue;
//    	assert lrVal.cType instanceof CPointer;//TODO -> must be a pointer or onHeap -- add a complicated assertion or let it be??
    	
        // Further checks are done in the precondition of ~free()!
        // ~free(E);
        CallStatement freeCall = new CallStatement(loc, false, new VariableLHS[0], SFO.DEALLOC,
                new Expression[] { lrVal.getValue() });
        // add required information to function handler.
        if (fh.getCurrentProcedureID() != null) {
            LinkedHashSet<String> mgM = new LinkedHashSet<String>();
            mgM.add(SFO.VALID);
            if (!fh.getModifiedGlobals().containsKey(SFO.DEALLOC)) {
                fh.getModifiedGlobals().put(SFO.DEALLOC, mgM);
                fh.getCallGraph().put(SFO.DEALLOC, new LinkedHashSet<String>());
            }
            fh.getCallGraph().get(fh.getCurrentProcedureID()).add(SFO.DEALLOC);
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
    	CPointer voidPointer = new CPointer(new CPrimitive(PRIMITIVE.VOID));
    	String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, voidPointer);
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, main.typeHandler.constructPointerType(loc), loc);
        
        LocalLValue llVal = new LocalLValue(new VariableLHS(loc, tmpId), voidPointer);
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
        
        String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD, m_ExpressionTranslation.getCTypeOfIntArray());
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
	        String bvtmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD, resultType);
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
    			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), 
    					"unsupported to write " + cType + " to heap");
    		} else {
    			throw new AssertionError("unable to write " + cType + " to heap");
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
			m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(cp.getType());
			return main.typeHandler.ctype2asttype(loc, ct);
		} else if (ut instanceof CPointer) {
			m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
			return main.typeHandler.constructPointerType(loc);
		} else if (ut instanceof CNamed) {
			assert false : "This should not be the case as we took the underlying type.";
			throw new UnsupportedSyntaxException(null, "non-heap type?: " + ct);
		} else if (ut instanceof CArray) {
			// we assume it is an Array on Heap
//			assert main.cHandler.isHeapVar(((IdentifierExpression) lrVal.getValue()).getIdentifier());
			//but it may not only be on heap, because it is addressoffed, but also because it is inside
			// a struct that is addressoffed..
			m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
			return main.typeHandler.constructPointerType(loc);
		} else if (ut instanceof CEnum) {
			//enum is treated like an int
			m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(PRIMITIVE.INT);
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
        	m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(((CPrimitive) valueType).getType());
        	switch (((CPrimitive) valueType).getGeneralType()) {
        	case INTTYPE:
        		m_FunctionHandler.getModifiedGlobals().
        			get(m_FunctionHandler.getCurrentProcedureID()).add(SFO.MEMORY_INT);
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.INT,
        				new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType())}));
        		break;
        	case FLOATTYPE:
        		m_FunctionHandler.getModifiedGlobals().
        			get(m_FunctionHandler.getCurrentProcedureID()).add(SFO.MEMORY_REAL);
        		stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.REAL,
        				new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType()) }));
        		break;	
        	default:
        		throw new UnsupportedSyntaxException(loc, "we don't recognize this type");
        	}
        } else if (valueType instanceof CEnum) {
        	//treat like INT
        	m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(PRIMITIVE.INT);
        	m_FunctionHandler.getModifiedGlobals().
        	get(m_FunctionHandler.getCurrentProcedureID()).add(SFO.MEMORY_INT);
        	stmt.add(new CallStatement(loc, false, new VariableLHS[0], "write~" + SFO.INT,
        			new Expression[] { value, hlv.getAddress(), this.calculateSizeOf(loc, hlv.getCType())}));
        } else if (valueType instanceof CPointer) {
        	m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
        	m_FunctionHandler.getModifiedGlobals().
        			get(m_FunctionHandler.getCurrentProcedureID()).add(SFO.MEMORY_POINTER);
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
        	m_FunctionHandler.getModifiedGlobals().
        			get(m_FunctionHandler.getCurrentProcedureID()).add(SFO.MEMORY_POINTER);
        	
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
			mallocs.add(this.getMallocCall(main, m_FunctionHandler, 
					llvp.llv, llvp.loc));
		ArrayList<Statement> frees = new ArrayList<Statement>();
		for (LocalLValueILocationPair llvp : this.variablesToBeFreed.currentScopeKeys()) {  //frees are inserted in handleReturnStm
			frees.add(this.getDeallocCall(main, m_FunctionHandler, llvp.llv, llvp.loc));
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
	


	public TypeSizeAndOffsetComputer getTypeSizeAndOffsetComputer() {
		return m_TypeSizeAndOffsetComputer;
	}
	

}
