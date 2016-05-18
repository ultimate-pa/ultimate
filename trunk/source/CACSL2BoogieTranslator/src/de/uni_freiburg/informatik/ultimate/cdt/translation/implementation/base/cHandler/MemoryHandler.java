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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.AMemoryModel.ReadWriteDefinition;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MEMORY_MODEL;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

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

	private final AExpressionTranslation m_ExpressionTranslation;
	
	private final TypeSizeAndOffsetComputer m_TypeSizeAndOffsetComputer;
	private final TypeSizes m_TypeSizes;
	private final RequiredMemoryModelFeatures m_RequiredMemoryModelFeatures;
	private final AMemoryModel m_MemoryModel;
	private final INameHandler m_NameHandler;
	private final MEMORY_MODEL m_MemoryModelPreference;
	private final IBooleanArrayHelper m_BooleanArrayHelper;
	
	
	/**
     * Constructor.
	 * @param typeHandler 
     * @param checkPointerValidity 
	 * @param typeSizeComputer 
	 * @param bitvectorTranslation 
	 * @param nameHandler 
     */
    public MemoryHandler(ITypeHandler typeHandler, FunctionHandler functionHandler, boolean checkPointerValidity, 
    		TypeSizeAndOffsetComputer typeSizeComputer, TypeSizes typeSizes, 
    		AExpressionTranslation expressionTranslation, boolean bitvectorTranslation, 
    		INameHandler nameHandler, boolean smtBoolArrayWorkaround) {
    	m_TypeHandler = typeHandler;
    	m_TypeSizes = typeSizes;
    	m_FunctionHandler = functionHandler;
    	m_ExpressionTranslation = expressionTranslation;
    	m_NameHandler = nameHandler;
    	m_RequiredMemoryModelFeatures = new RequiredMemoryModelFeatures();
    	if (smtBoolArrayWorkaround) {
    		if (bitvectorTranslation) {
    			m_BooleanArrayHelper = new BooleanArrayHelper_Bitvector();
    		} else {
    			m_BooleanArrayHelper = new BooleanArrayHelper_Integer();
    		}
    	} else {
    		m_BooleanArrayHelper = new BooleanArrayHelper_Bool();
    	}
    	

		//read preferences from settings
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		m_PointerBaseValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, POINTER_CHECKMODE.class);
    	m_PointerTargetFullyAllocated = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, POINTER_CHECKMODE.class);
    	m_CheckFreeValid = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
    	m_checkPointerSubtractionAndComparisonValidity = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY, POINTER_CHECKMODE.class);
    	m_MemoryModelPreference = 
    			ups.getEnum(CACSLPreferenceInitializer.LABEL_MEMORY_MODEL, MEMORY_MODEL.class);
    	final MEMORY_MODEL memoryModelPreference = m_MemoryModelPreference;
    	final AMemoryModel memoryModel = getMemoryModel(bitvectorTranslation, memoryModelPreference);
    	m_MemoryModel = memoryModel;
		variablesToBeMalloced = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		variablesToBeFreed = new LinkedScopedHashMap<LocalLValueILocationPair, Integer>();
		
		m_TypeSizeAndOffsetComputer = typeSizeComputer;
    }



	private AMemoryModel getMemoryModel(boolean bitvectorTranslation, final MEMORY_MODEL memoryModelPreference)
			throws AssertionError {
		final AMemoryModel memoryModel;
    	if (bitvectorTranslation) {
    		switch (memoryModelPreference) {
			case HoenickeLindenmann_1ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(1, m_TypeSizes, (TypeHandler) m_TypeHandler, m_ExpressionTranslation);
				break;
			case HoenickeLindenmann_2ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(2, m_TypeSizes, (TypeHandler) m_TypeHandler, m_ExpressionTranslation);
				break;
			case HoenickeLindenmann_4ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(4, m_TypeSizes, (TypeHandler) m_TypeHandler, m_ExpressionTranslation);
				break;
			case HoenickeLindenmann_8ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(8, m_TypeSizes, (TypeHandler) m_TypeHandler, m_ExpressionTranslation);
				break;
			case HoenickeLindenmann_Original:
				memoryModel = new MemoryModel_MultiBitprecise(m_TypeSizes, m_TypeHandler, m_ExpressionTranslation);
				break;
			default:
				throw new AssertionError("unknown value");
    		}
    	} else {
    		switch (memoryModelPreference) {
			case HoenickeLindenmann_Original:
				memoryModel = new MemoryModel_Unbounded(m_TypeSizes, m_TypeHandler, m_ExpressionTranslation);
				break;
			case HoenickeLindenmann_1ByteResolution:
			case HoenickeLindenmann_2ByteResolution:
			case HoenickeLindenmann_4ByteResolution:
			case HoenickeLindenmann_8ByteResolution:
				throw new UnsupportedOperationException("Memory model " + 
						m_MemoryModelPreference + " only available in bitprecise translation");
			default:
				throw new AssertionError("unknown value");
    		}
    	}
		return memoryModel;
	}
    
    
    
    public RequiredMemoryModelFeatures getRequiredMemoryModelFeatures() {
		return m_RequiredMemoryModelFeatures;
	}



	public AMemoryModel getMemoryModel() {
		return m_MemoryModel;
	}


	public enum MemoryModelDeclarations {
		Ultimate_Alloc("#Ultimate.alloc"),
		Ultimate_MemInit("#Ultimate.meminit"), 
		C_Memcpy("#Ultimate.C_memcpy"),
		C_Memset("#Ultimate.C_memset");
		
	
		MemoryModelDeclarations(String name) {
			m_Name = name;
		}
		private final String m_Name;
		
		public String getName() {
			return m_Name;
		}
	
	};

	public class RequiredMemoryModelFeatures {
		
    	private final Set<PRIMITIVE> m_DataOnHeapRequired = new HashSet<>();
    	private boolean m_PointerOnHeapRequired;
    	private final Set<MemoryModelDeclarations> m_RequiredMemoryModelDeclarations = new HashSet<>();
    	
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
    	
		public boolean isMemoryModelInfrastructureRequired() {
			return isPointerOnHeapRequired() || !getDataOnHeapRequired().isEmpty();
		}
		
		public boolean require(MemoryModelDeclarations mmdecl) {
			return m_RequiredMemoryModelDeclarations.add(mmdecl);
		}

		public Set<MemoryModelDeclarations> getRequiredMemoryModelDeclarations() {
			return Collections.unmodifiableSet(m_RequiredMemoryModelDeclarations);
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
        if (!main.isMMRequired() && 
        		!m_RequiredMemoryModelFeatures.isMemoryModelInfrastructureRequired() &&
        		m_RequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().isEmpty()) {
            return decl;
        }

        decl.add(constructNullPointerConstant());
        decl.add(constructValidArrayDeclaration());
        decl.add(constuctLengthArrayDeclaration());

        Collection<HeapDataArray> heapDataArrays = m_MemoryModel.getDataHeapArrays(m_RequiredMemoryModelFeatures);

        {// add memory arrays and read/write procedures
        	for (HeapDataArray heapDataArray : heapDataArrays) {
        		decl.add(constructMemoryArrayDeclaration(tuLoc, heapDataArray.getName(), heapDataArray.getASTType()));
        		// create and add read and write procedure
        		decl.addAll(constructWriteProcedures(tuLoc, heapDataArrays, heapDataArray));
        		decl.addAll(constructReadProcedures(tuLoc, heapDataArray));
        	}
        }

        decl.addAll(declareFree(main, tuLoc));
        decl.addAll(declareDeallocation(main, tuLoc));
        
        if (m_RequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().contains(MemoryModelDeclarations.Ultimate_Alloc)) {
        	decl.addAll(declareMalloc(m_TypeHandler, tuLoc));
        	m_FunctionHandler.registerProcedureForCallGraphAndModifies(MemoryModelDeclarations.Ultimate_Alloc.getName());
        }

        if (m_RequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().contains(MemoryModelDeclarations.C_Memset)) {
        	decl.addAll(declareMemset(main, heapDataArrays));
        	m_FunctionHandler.registerProcedureForCallGraphAndModifies(MemoryModelDeclarations.C_Memset.getName());
        }
        
        if (m_RequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().contains(MemoryModelDeclarations.Ultimate_MemInit)) {
        	decl.addAll(declareUltimateMeminit(main, heapDataArrays));
        	m_FunctionHandler.registerProcedureForCallGraphAndModifies(MemoryModelDeclarations.Ultimate_MemInit.getName());
        }
        
        if (m_RequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().contains(MemoryModelDeclarations.C_Memcpy)) {
        	decl.addAll(declareMemcpy(main, heapDataArrays));
        	m_FunctionHandler.registerProcedureForCallGraphAndModifies(MemoryModelDeclarations.C_Memcpy.getName());
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
                new ASTType[] { pointerComponentType }, m_BooleanArrayHelper.constructBoolReplacementType());
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
	
	
    private List<Declaration> declareUltimateMeminit(Dispatcher main,
    		Collection<HeapDataArray> heapDataArrays) {
    	ArrayList<Declaration> decls = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	String inParamPtr = "#ptr";
    	String inParamAmountOfFields = "#amountOfFields";
    	String inParamSizeOfFields = "#sizeOfFields";
    	String inParamProduct = "#product";
    	String proc = MemoryModelDeclarations.Ultimate_MemInit.getName();
    	
    	VarList inParamPtrVl = new VarList(ignoreLoc, new String[] { inParamPtr }, 
    			m_TypeHandler.constructPointerType(ignoreLoc));
    	VarList inParamAmountOfFieldsVl = new VarList(ignoreLoc, new String[] { inParamAmountOfFields }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T()));
    	VarList inParamSizeOfFieldsVl = new VarList(ignoreLoc, new String[] { inParamSizeOfFields }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T()));
    	VarList inParamProductVl = new VarList(ignoreLoc, new String[] { inParamProduct }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T()));
    	
    	VarList[] inParams = new VarList[] { inParamPtrVl, inParamAmountOfFieldsVl, inParamSizeOfFieldsVl, inParamProductVl };
    	VarList[] outParams = new VarList[] { };
   			
    	List<VariableDeclaration> decl = new ArrayList<>();
    	CPrimitive sizeT = m_TypeSizeAndOffsetComputer.getSize_T();
    	String loopCtr = m_NameHandler.getTempVarUID(SFO.AUXVAR.LOOPCTR, sizeT);
    	ASTType astType = m_TypeHandler.ctype2asttype(ignoreLoc, sizeT);
		VarList lcvl = new VarList(ignoreLoc, new String[] { loopCtr }, astType);
		VariableDeclaration loopCtrDec = new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { lcvl });
		decl.add(loopCtrDec);

		Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, new CPrimitive(PRIMITIVE.UCHAR), BigInteger.ZERO);
		List<Statement> loopBody = constructMemsetLoopBody(heapDataArrays, loopCtr, inParamPtr, zero);
		
		IdentifierExpression inParamProductExpr = new IdentifierExpression(ignoreLoc, inParamProduct);
		final Expression stepsize;
		if (m_MemoryModel instanceof MemoryModel_SingleBitprecise) {
			int resolution = ((MemoryModel_SingleBitprecise) m_MemoryModel).getResolution();
			stepsize = m_ExpressionTranslation.constructLiteralForIntegerType(ignoreLoc, sizeT, BigInteger.valueOf(resolution));
		} else {
			IdentifierExpression inParamSizeOfFieldsExpr = new IdentifierExpression(ignoreLoc, inParamSizeOfFields);
			stepsize = inParamSizeOfFieldsExpr;
		}
		
		List<Statement> stmt = constructCountingLoop(inParamProductExpr, loopCtr, stepsize, loopBody);
		
		Body procBody = new Body(ignoreLoc, 
				decl.toArray(new VariableDeclaration[decl.size()]), 
				stmt.toArray(new Statement[stmt.size()]));
		
		//make the specifications
		ArrayList<Specification> specs = new ArrayList<>();
		
		// add modifies spec
		ModifiesSpecification modifiesSpec = announceModifiedGlobals(proc, heapDataArrays);
		specs.add(modifiesSpec);
		
		//add the procedure declaration
     	Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], proc, new String[0], 
    			inParams, outParams, specs.toArray(new Specification[specs.size()]), null);
     	decls.add(memCpyProcDecl);
     	
     	//add the procedure implementation
     	Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], proc, new String[0], 
    			inParams, outParams, null, procBody);
     	decls.add(memCpyProc);
    	
		return decls;
	}
    
	public CallStatement constructUltimateMeminitCall(ILocation loc, Expression amountOfFields, Expression sizeOfFields,
			Expression product, Expression pointer) {
		m_RequiredMemoryModelFeatures.require(MemoryModelDeclarations.Ultimate_MemInit);
		return new CallStatement(loc, false, new VariableLHS[0], MemoryModelDeclarations.Ultimate_MemInit.getName(),
				new Expression[] { pointer, amountOfFields, sizeOfFields, product });
	}

    /**
     * Tell m_FunctionHandler that procedure proc modifies all heapDataArrays.
     * Retruns modifies specification.
     */
	private ModifiesSpecification announceModifiedGlobals(String proc,
			Collection<HeapDataArray> heapDataArrays) {
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		ArrayList<VariableLHS> modifiesLHSs = new ArrayList<>();
		for (HeapDataArray hda : heapDataArrays) {
			String memArrayName = hda.getVariableName();
			modifiesLHSs.add(new VariableLHS(ignoreLoc, memArrayName));

			if (m_FunctionHandler.getModifiedGlobals().get(proc) == null){
				m_FunctionHandler.getModifiedGlobals().put(proc, new LinkedHashSet<String>());
			}
			if (m_FunctionHandler.getCallGraph().get(proc) == null) {
				m_FunctionHandler.getCallGraph().put(proc, new LinkedHashSet<String>());
			}
			m_FunctionHandler.getModifiedGlobals().get(proc).add(memArrayName);
		}
		return new ModifiesSpecification(ignoreLoc, false, 
				modifiesLHSs.toArray(new VariableLHS[modifiesLHSs.size()]));
	}
	
	

    /**
     * Construct specification and implementation for our Boogie representation
     * of the memcpy function defined in 7.24.2.1 of C11.
     * void *memcpy(void * restrict s1, const void * restrict s2, size_t n);
     * @param main
     * @param heapDataArrays
     * @return
     */
    private List<Declaration> declareMemcpy(Dispatcher main,
    		Collection<HeapDataArray> heapDataArrays) {
    	ArrayList<Declaration> memCpyDecl = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	String memcpyInParamSize = SFO.MEMCPY_SIZE;
    	String memcpyInParamDest = SFO.MEMCPY_DEST;
    	String memcpyInParamSrc = SFO.MEMCPY_SRC;
    	String memcpyOutParam = SFO.RES;
    	
    	VarList inPDest = new VarList(ignoreLoc, new String[] { memcpyInParamDest }, m_TypeHandler.constructPointerType(ignoreLoc));
    	VarList inPSrc = new VarList(ignoreLoc, new String[] { memcpyInParamSrc }, m_TypeHandler.constructPointerType(ignoreLoc));
    	VarList	inPSize = new VarList(ignoreLoc, new String[] { memcpyInParamSize }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T()));
    	VarList outP = new VarList(ignoreLoc, new String[] { memcpyOutParam }, m_TypeHandler.constructPointerType(ignoreLoc));
    	VarList[] inParams = new VarList[] { inPDest, inPSrc, inPSize };
    	VarList[] outParams = new VarList[] { outP };

   			
    	List<VariableDeclaration> decl = new ArrayList<>();
    	CPrimitive sizeT = m_TypeSizeAndOffsetComputer.getSize_T();
    	String loopCtr = m_NameHandler.getTempVarUID(SFO.AUXVAR.LOOPCTR, sizeT);
    	ASTType astType = m_TypeHandler.ctype2asttype(ignoreLoc, sizeT);
		VarList lcvl = new VarList(ignoreLoc, new String[] { loopCtr }, astType);
		VariableDeclaration loopCtrDec = new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { lcvl });
		decl.add(loopCtrDec);

		List<Statement> loopBody = constructMemcpyLoopBody(heapDataArrays, loopCtr, memcpyInParamDest, memcpyInParamSrc);
		
		IdentifierExpression memcpyInParamSizeExpr = new IdentifierExpression(ignoreLoc, memcpyInParamSize);
		Expression one = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
		List<Statement> stmt = constructCountingLoop(memcpyInParamSizeExpr, loopCtr, one, loopBody);
		
		Body procBody = new Body(ignoreLoc, 
				decl.toArray(new VariableDeclaration[decl.size()]), 
				stmt.toArray(new Statement[stmt.size()]));
		
		//make the specifications
		ArrayList<Specification> specs = new ArrayList<>();
		
		// add modifies spec
		ModifiesSpecification modifiesSpec = announceModifiedGlobals(MemoryModelDeclarations.C_Memcpy.getName(), heapDataArrays);
		specs.add(modifiesSpec);
		
		// add requires #valid[dest!base];
        addPointerBaseValidityCheck(ignoreLoc, memcpyInParamDest, specs);
        // add requires #valid[src!base];
        addPointerBaseValidityCheck(ignoreLoc, memcpyInParamSrc, specs);
        
        Expression memcpyParamSizeExpr = new IdentifierExpression(ignoreLoc, memcpyInParamSize);

        // add requires size + dest!offset <= #length[dest!base];
        checkPointerTargetFullyAllocated(ignoreLoc, memcpyParamSizeExpr, memcpyInParamDest, specs);
        
        // add requires size + src!offset <= #length[src!base];
        checkPointerTargetFullyAllocated(ignoreLoc, memcpyParamSizeExpr, memcpyInParamSrc, specs);
        
        // free ensures #res == dest;
        EnsuresSpecification returnValue = new EnsuresSpecification(ignoreLoc, 
        		true, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ, 
        		new IdentifierExpression(ignoreLoc, memcpyOutParam),
        		new IdentifierExpression(ignoreLoc, memcpyInParamDest)));
        specs.add(returnValue);
        
        
		//add the procedure declaration
     	Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], 
     			MemoryModelDeclarations.C_Memcpy.getName(), new String[0], 
    			inParams, outParams, specs.toArray(new Specification[specs.size()]), null);
     	memCpyDecl.add(memCpyProcDecl);
     	
     	//add the procedure implementation
     	Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], 
     			MemoryModelDeclarations.C_Memcpy.getName(), new String[0], 
    			inParams, outParams, null, procBody);
     	memCpyDecl.add(memCpyProc);
    	
		return memCpyDecl;
	}
    
    /**
     * Returns call to our memcpy procedure and announces that memcpy is 
     * required by our memory model. 
     */
	public CallStatement constructMemcpyCall(ILocation loc, Expression dest, Expression src,
			Expression size, String resVarId) {
		m_RequiredMemoryModelFeatures.require(MemoryModelDeclarations.C_Memcpy);
		return new CallStatement(loc, false, new VariableLHS[] { new VariableLHS(loc, resVarId) }, MemoryModelDeclarations.C_Memcpy.getName(), 
				new Expression[] { dest, src, size });
	}
    

    /**
     * Construct loop of the following form, where loopBody is a List of 
     * statements and the variables loopConterVariable and loopBoundVariable
     * have the translated type of size_t.
     * 
     * loopConterVariable := 0;
     * while (#t~loopctr4 < loopBoundVariable) {
     *    ___loopBody___
     *    loopConterVariable := loopConterVariable + 1;
     * }
     * 
     * @param loopBoundVariableExpr
     * @param loopCounterVariableId
     * @param loopBody
     * @return
     */
	private ArrayList<Statement> constructCountingLoop(Expression loopBoundVariableExpr, 
			String loopCounterVariableId, Expression loopCounterIncrementExpr,
			List<Statement> loopBody) {
		CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		ArrayList<Statement> stmt = new ArrayList<>();
		
		//initialize the counter to 0
		Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T(), BigInteger.ZERO);
		stmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { new VariableLHS(ignoreLoc, loopCounterVariableId)}, 
				new Expression[] { zero }));
		
		IdentifierExpression loopCounterVariableExpr = new IdentifierExpression(ignoreLoc, loopCounterVariableId);
		
		Expression condition = m_ExpressionTranslation.constructBinaryComparisonExpression(
				ignoreLoc, IASTBinaryExpression.op_lessThan, 
				loopCounterVariableExpr, m_TypeSizeAndOffsetComputer.getSize_T(), 
				loopBoundVariableExpr, m_TypeSizeAndOffsetComputer.getSize_T());
		
		ArrayList<Statement> bodyStmt = new ArrayList<>();
		bodyStmt.addAll(loopBody);
		
		//increment counter
		VariableLHS ctrLHS = new VariableLHS(ignoreLoc, loopCounterVariableId);
		Expression counterPlusOne = m_ExpressionTranslation.constructArithmeticExpression(
				ignoreLoc, IASTBinaryExpression.op_plus, 
				loopCounterVariableExpr, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
				loopCounterIncrementExpr, m_ExpressionTranslation.getCTypeOfPointerComponents());
		bodyStmt.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { ctrLHS }, 
				new Expression[] { counterPlusOne }));
		
		Statement[] whileBody = bodyStmt.toArray(new Statement[bodyStmt.size()]);
		
		WhileStatement whileStm = new WhileStatement(ignoreLoc, condition, new LoopInvariantSpecification[0], whileBody); 
		stmt.add(whileStm);
		return stmt;
	}

	/**
	 * Return the assignments that we do in the loop body of our memcpy 
	 * implementation.
	 * 
	 * #memory_int[{ base: dest!base, offset: dest!offset + #t~loopctr6 * 1 }] := #memory_int[{ base: src!base, offset: src!offset + #t~loopctr6 * 1 }];
	 * @param heapDataArrays
	 * @param loopCtr
	 * @param destPtr
	 * @param srcPtr
	 * @return
	 */
	private ArrayList<Statement> constructMemcpyLoopBody(Collection<HeapDataArray> heapDataArrays, 
			String loopCtr, String destPtr, String srcPtr) {
		
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		ArrayList<Statement> result = new ArrayList<>();
		
		IdentifierExpression loopCtrExpr = new IdentifierExpression(ignoreLoc, loopCtr);
		IdentifierExpression destPtrExpr = new IdentifierExpression(ignoreLoc, destPtr);
		IdentifierExpression srcPtrExpr = new IdentifierExpression(ignoreLoc, srcPtr);

		Expression currentDest = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, destPtrExpr, 
				new RValue(loopCtrExpr, m_ExpressionTranslation.getCTypeOfPointerComponents()), 
				new CPrimitive(PRIMITIVE.VOID));
		Expression currentSrc = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, srcPtrExpr, 
				new RValue(loopCtrExpr, m_ExpressionTranslation.getCTypeOfPointerComponents()), 
				new CPrimitive(PRIMITIVE.VOID));
		for (HeapDataArray hda : heapDataArrays) {
			String memArrayName = hda.getVariableName();
			ArrayAccessExpression srcAcc = new ArrayAccessExpression(ignoreLoc, new IdentifierExpression(ignoreLoc, memArrayName), new Expression[] { currentSrc });
			ArrayLHS destAcc = new ArrayLHS(ignoreLoc, new VariableLHS(ignoreLoc, memArrayName), new Expression[] { currentDest });
			result.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { destAcc }, new Expression[] { srcAcc }));
			
		}
		return result;
	}
	
	private ArrayList<Statement> constructMemsetLoopBody(Collection<HeapDataArray> heapDataArrays, 
			String loopCtr, String ptr, Expression valueExpr) {
		
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		ArrayList<Statement> result = new ArrayList<>();
		
		IdentifierExpression loopCtrExpr = new IdentifierExpression(ignoreLoc, loopCtr);
		IdentifierExpression ptrExpr = new IdentifierExpression(ignoreLoc, ptr);

		Expression currentPtr = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, ptrExpr, 
				new RValue(loopCtrExpr, m_ExpressionTranslation.getCTypeOfPointerComponents()), 
				new CPrimitive(PRIMITIVE.VOID));
		for (HeapDataArray hda : heapDataArrays) {
			final Expression convertedValue;
			final ExpressionResult exprRes = new ExpressionResult(new RValue(valueExpr, new CPrimitive(PRIMITIVE.UCHAR)));
			if (hda.getName().equals(SFO.POINTER)) {
				m_ExpressionTranslation.convertIntToInt(ignoreLoc, exprRes, m_ExpressionTranslation.getCTypeOfPointerComponents());
				Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(ignoreLoc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
				convertedValue = constructPointerFromBaseAndOffset(zero, exprRes.lrVal.getValue(), ignoreLoc);
			} else {
				// convert to smallest
				List<ReadWriteDefinition> rwds = m_MemoryModel.getReadWriteDefinitionForHeapDataArray(hda, getRequiredMemoryModelFeatures());
//				PRIMITIVE primitive = getCprimitiveThatFitsBest(rwds);
				PRIMITIVE primitive = getCprimitiveThatFitsBest(hda.getSize());
				m_ExpressionTranslation.convertIntToInt(ignoreLoc, exprRes, new CPrimitive(primitive));
				convertedValue = exprRes.lrVal.getValue();
			}
			String memArrayName = hda.getVariableName();
			ArrayLHS destAcc = new ArrayLHS(ignoreLoc, new VariableLHS(ignoreLoc, memArrayName), new Expression[] { currentPtr });
			
			result.add(new AssignmentStatement(ignoreLoc, new LeftHandSide[] { destAcc }, new Expression[] { convertedValue }));
		}
		return result;
	}
    
	/**
	 * Returns an CPrimitive which is unsigned, integer and not bool that has
	 * the smallest bytesize.
	 */
    private PRIMITIVE getCprimitiveThatFitsBest(List<ReadWriteDefinition> test) {
    	int smallestBytesize = Integer.MAX_VALUE;
    	for (ReadWriteDefinition rwd : test) {
    		if (rwd.getBytesize() < smallestBytesize) {
    			smallestBytesize = rwd.getBytesize();
    		}
    	}
    	if (smallestBytesize == 0) {
    		// we only have unbounded data types
    		return PRIMITIVE.UCHAR;
    	}
    	for (PRIMITIVE primitive : new PRIMITIVE[] { PRIMITIVE.UCHAR, PRIMITIVE.USHORT, 
    			PRIMITIVE.UINT, PRIMITIVE.ULONG, PRIMITIVE.ULONGLONG}) {
    		if (m_TypeSizes.getSize(primitive) == smallestBytesize) {
    			return primitive;
    		}
    	}
    	throw new AssertionError("don't know how to store value on heap");
    }
    
	/**
	 * Returns an CPrimitive which is unsigned, integer and not bool that has
	 * the smallest bytesize.
	 */
    private PRIMITIVE getCprimitiveThatFitsBest(int byteSize) {
    	if (byteSize == 0) {
    		// we only have unbounded data types
    		return PRIMITIVE.UCHAR;
    	}
    	for (PRIMITIVE primitive : new PRIMITIVE[] { PRIMITIVE.UCHAR, PRIMITIVE.USHORT, 
    			PRIMITIVE.UINT, PRIMITIVE.ULONG, PRIMITIVE.ULONGLONG}) {
    		if (m_TypeSizes.getSize(primitive) == byteSize) {
    			return primitive;
    		}
    	}
    	throw new AssertionError("don't know how to store value on heap");
    }
    
    /**
     * Construct specification and implementation for our Boogie representation
     * of the memset function defined in 7.24.6.1 of C11.
     * void *memset(void *s, int c, size_t n);
     * @param main
     * @param heapDataArrays
     * @return
     */
    private List<Declaration> declareMemset(Dispatcher main,
    		Collection<HeapDataArray> heapDataArrays) {
    	ArrayList<Declaration> decls = new ArrayList<>();
    	ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
    	
    	String inParamPtr = "#ptr";
    	String inParamValue = "#value";
    	String inParamAmount = "#amount";
    	String outParamResult= "#res";
    	String proc = MemoryModelDeclarations.C_Memset.getName();
    	
    	VarList inParamPtrVl = new VarList(ignoreLoc, new String[] { inParamPtr }, 
    			m_TypeHandler.constructPointerType(ignoreLoc));
    	VarList inParamValueVl = new VarList(ignoreLoc, new String[] { inParamValue }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, new CPrimitive(PRIMITIVE.INT)));
    	VarList inParamAmountVl = new VarList(ignoreLoc, new String[] { inParamAmount }, 
    			m_TypeHandler.ctype2asttype(ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T()));
    	VarList outParamResultVl = new VarList(ignoreLoc, new String[] { outParamResult }, 
    			m_TypeHandler.constructPointerType(ignoreLoc));
    	
    	VarList[] inParams = new VarList[] { inParamPtrVl, inParamValueVl, inParamAmountVl };
    	VarList[] outParams = new VarList[] { outParamResultVl };
   			
    	List<VariableDeclaration> decl = new ArrayList<>();
    	CPrimitive sizeT = m_TypeSizeAndOffsetComputer.getSize_T();
    	String loopCtr = m_NameHandler.getTempVarUID(SFO.AUXVAR.LOOPCTR, sizeT);
    	ASTType astType = m_TypeHandler.ctype2asttype(ignoreLoc, sizeT);
		VarList lcvl = new VarList(ignoreLoc, new String[] { loopCtr }, astType);
		VariableDeclaration loopCtrDec = new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { lcvl });
		decl.add(loopCtrDec);
		
		// converted value to unsigned char
		IdentifierExpression inParamValueExpr = new IdentifierExpression(ignoreLoc, inParamValue);
		ExpressionResult exprRes = new ExpressionResult(new RValue(inParamValueExpr, new CPrimitive(PRIMITIVE.INT)));
		m_ExpressionTranslation.convertIntToInt(ignoreLoc, exprRes, new CPrimitive(PRIMITIVE.UCHAR));
		Expression convertedValue = exprRes.lrVal.getValue();

		List<Statement> loopBody = constructMemsetLoopBody(heapDataArrays, loopCtr, inParamPtr, convertedValue);
		
		Expression one = m_ExpressionTranslation.constructLiteralForIntegerType(
				ignoreLoc, m_TypeSizeAndOffsetComputer.getSize_T(), BigInteger.ONE);
		IdentifierExpression inParamAmountExpr = new IdentifierExpression(ignoreLoc, inParamAmount);
		List<Statement> stmt = constructCountingLoop(inParamAmountExpr, loopCtr, one, loopBody);
		
		Body procBody = new Body(ignoreLoc, 
				decl.toArray(new VariableDeclaration[decl.size()]), 
				stmt.toArray(new Statement[stmt.size()]));
		
		//make the specifications
		ArrayList<Specification> specs = new ArrayList<>();
		
		// add modifies spec
		ModifiesSpecification modifiesSpec = announceModifiedGlobals(proc, heapDataArrays);
		specs.add(modifiesSpec);
		
		// add requires #valid[#ptr!base];
        addPointerBaseValidityCheck(ignoreLoc, inParamPtr, specs);

        // add requires size + #ptr!offset <= #length[#ptr!base];
        checkPointerTargetFullyAllocated(ignoreLoc, inParamAmountExpr, inParamPtr, specs);
        
        
        // free ensures #res == dest;
        EnsuresSpecification returnValue = new EnsuresSpecification(ignoreLoc, 
        		true, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ, 
        		new IdentifierExpression(ignoreLoc, outParamResult),
        		new IdentifierExpression(ignoreLoc, inParamPtr)));
        specs.add(returnValue);
		
		//add the procedure declaration
     	Procedure procDecl = new Procedure(ignoreLoc, new Attribute[0], proc, new String[0], 
    			inParams, outParams, specs.toArray(new Specification[specs.size()]), null);
     	decls.add(procDecl);
     	
     	//add the procedure implementation
     	Procedure procImpl = new Procedure(ignoreLoc, new Attribute[0], proc, new String[0], 
    			inParams, outParams, null, procBody);
     	decls.add(procImpl);
    	
		return decls;
	}
    
    /**
     * Returns call to our memset procedure and announces that memset is 
     * required by our memory model. 
     */
	public CallStatement constructUltimateMemsetCall(ILocation loc, Expression pointer, Expression value,
			Expression amount, String resVarId) {
		m_RequiredMemoryModelFeatures.require(MemoryModelDeclarations.C_Memset);
		return new CallStatement(loc, false, new VariableLHS[] { new VariableLHS(loc, resVarId) }, MemoryModelDeclarations.C_Memset.getName(),
				new Expression[] { pointer, value, amount });
	}
    
    		
	private VariableDeclaration constructMemoryArrayDeclaration(
			final ILocation loc, final String typeName, final ASTType astType) {
		final ASTType memoryArrayType = new ArrayType(loc, new String[0],
		        new ASTType[] { m_TypeHandler.constructPointerType(loc) }, astType);
		final VarList varList = new VarList(loc, new String[] { SFO.MEMORY + "_" 
		        + typeName }, memoryArrayType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { varList });
	}
	

	private List<Declaration> constructWriteProcedures(ILocation loc, Collection<HeapDataArray> heapDataArrays,
			HeapDataArray heapDataArray) {
		List<Declaration> result = new ArrayList<>();
		for (ReadWriteDefinition rda : m_MemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray, m_RequiredMemoryModelFeatures)) {
			result.add(constructWriteProcedure(loc, heapDataArrays, heapDataArray, rda));
		}
		return result;
	}
	
	private List<Declaration> constructReadProcedures(ILocation loc, HeapDataArray heapDataArray) {
		List<Declaration> result = new ArrayList<>();
		for (ReadWriteDefinition rda : m_MemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray, m_RequiredMemoryModelFeatures)) {
			result.add(constructReadProcedure(loc, heapDataArray, rda));
		}
		return result;
	}

	private Procedure constructWriteProcedure(final ILocation loc, 
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray,
			ReadWriteDefinition rda) {
		String value = "#value";
		final ASTType valueAstType = rda.getASTType();
		String inPtr = "#ptr";
		String writtenTypeSize = "#sizeOfWrittenType";

		ASTType sizetType = m_TypeHandler.ctype2asttype(loc, m_TypeSizeAndOffsetComputer.getSize_T());
		VarList[] inWrite = new VarList[] {
				new VarList(loc, new String[] { value }, valueAstType),
				new VarList(loc, new String[] { inPtr }, m_TypeHandler.constructPointerType(loc)),
				new VarList(loc, new String[] { writtenTypeSize }, sizetType) };
         
		// specification for memory writes
		ArrayList<Specification> swrite = new ArrayList<Specification>();

		addPointerBaseValidityCheck(loc, inPtr, swrite);

		Expression sizeWrite = new IdentifierExpression(loc, writtenTypeSize);
		checkPointerTargetFullyAllocated(loc, sizeWrite, inPtr, swrite);

		ModifiesSpecification mod = constructModifiesSpecification(loc, heapDataArrays, x -> x.getVariableName());
		swrite.add(mod);
		if (rda.getBytesize() == heapDataArray.getSize()) {
			addWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray, value, x -> x, inPtr, x -> x, swrite);
		} else if (rda.getBytesize() < heapDataArray.getSize()) {
			final Function<Expression, Expression> valueExtension = x -> m_ExpressionTranslation.signExtend(loc, x, rda.getBytesize()*8, heapDataArray.getSize()*8);
			addWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray, value, valueExtension, inPtr, x -> x, swrite);
		} else {
			assert rda.getBytesize() % heapDataArray.getSize() == 0 : "incompatible sizes";
			for (int i=0; i<rda.getBytesize()/heapDataArray.getSize(); i++) {
				final Function<Expression, Expression> extractBits;
				final int currentI = i;
				extractBits = x -> m_ExpressionTranslation.extractBits(loc, x, heapDataArray.getSize()*(currentI+1)*8, heapDataArray.getSize()*currentI*8);
				if (i==0) {
					addWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray, value, extractBits, inPtr, x -> x, swrite);
				} else {
					final BigInteger additionalOffset = BigInteger.valueOf(i*heapDataArray.getSize());
					final Function<Expression, Expression> pointerAddition = 
							x -> addIntegerConstantToPointer(loc, x, additionalOffset);
					addWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray, value, extractBits, inPtr, pointerAddition, swrite);
				}
			}
		}

		Procedure result = new Procedure(loc, new Attribute[0], rda.getWriteProcedureName(), new String[0],
				inWrite, new VarList[0], swrite.toArray(new Specification[swrite.size()]), null);
		return result;
	}

	private void addWriteEnsuresSpecification(final ILocation loc, 
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray, 
			String value, Function<Expression, Expression> valueModification, 
			String inPtr, Function<Expression, Expression> ptrModification,
			ArrayList<Specification> swrite) {
		for (HeapDataArray other : heapDataArrays) {
			if (heapDataArray == other) {
				swrite.add(ensuresHeapArrayUpdate(loc, value, valueModification, inPtr, ptrModification, other));
			} else {
				swrite.add(ensuresHeapArrayHardlyModified(loc, inPtr, ptrModification, other));
			}

		}
	}

	private Procedure constructReadProcedure(final ILocation loc, HeapDataArray hda, ReadWriteDefinition rda) {
		// specification for memory reads
		final String value = "#value";
		final ASTType valueAstType = rda.getASTType();
		final String ptrId = "#ptr";
		final String readTypeSize = "#sizeOfReadType";
		ASTType sizetType = m_TypeHandler.ctype2asttype(loc, m_TypeSizeAndOffsetComputer.getSize_T());
		VarList[] inRead = new VarList[] { 
				new VarList(loc, new String[] { ptrId }, m_TypeHandler.constructPointerType(loc)),
				new VarList(loc, new String[] { readTypeSize }, sizetType) };
		VarList[] outRead = new VarList[] { new VarList(loc,
		        new String[] { value }, valueAstType) };
		
		ArrayList<Specification> sread = new ArrayList<Specification>();
		
		addPointerBaseValidityCheck(loc, ptrId, sread);
		
		Expression sizeRead = new IdentifierExpression(loc, readTypeSize);
		checkPointerTargetFullyAllocated(loc, sizeRead, ptrId, sread);
		
		Expression arr = new IdentifierExpression(loc, hda.getVariableName());
		Expression ptrExpr = new IdentifierExpression(loc, ptrId);
		
		final Expression dataFromHeap;
		if (rda.getBytesize() == hda.getSize()) {
			dataFromHeap = constructOneDimensionalArrayAccess(loc, arr, ptrExpr);
		} else if (rda.getBytesize() < hda.getSize()) {
			dataFromHeap = m_ExpressionTranslation.extractBits(loc, 
					constructOneDimensionalArrayAccess(loc, arr, ptrExpr), rda.getBytesize() * 8, 0);
		} else {
			assert rda.getBytesize() % hda.getSize() == 0 : "incompatible sizes";
			Expression[] dataChunks = new Expression[rda.getBytesize() / hda.getSize()];
			for (int i=0; i<dataChunks.length; i++) {
				if (i==0) {
					dataChunks[dataChunks.length-1 - 0] = constructOneDimensionalArrayAccess(loc, arr, ptrExpr);
				} else {
					Expression index = addIntegerConstantToPointer(loc, ptrExpr, BigInteger.valueOf(i*hda.getSize()));
					dataChunks[dataChunks.length-1 - i] = constructOneDimensionalArrayAccess(loc, arr, index);
				}
			}
			dataFromHeap = m_ExpressionTranslation.concatBits(loc, Arrays.asList(dataChunks), hda.getSize());
		}
		Expression valueExpr = new IdentifierExpression(loc, value);
		Expression equality = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, valueExpr, dataFromHeap);
		sread.add(new EnsuresSpecification(loc, false, equality));
		Procedure result = new Procedure(loc, new Attribute[0], rda.getReadProcedureName(), new String[0],
		        inRead, outRead, sread.toArray(new Specification[0]), null);
		return result;
	}
	
	private Expression addIntegerConstantToPointer(ILocation loc, Expression ptrExpr, BigInteger integerConstant) {
		final Expression base = getPointerBaseAddress(ptrExpr, loc);
		final Expression offset = getPointerOffset(ptrExpr, loc);
		final Expression addition = m_ExpressionTranslation.constructLiteralForIntegerType(
				loc, m_TypeSizeAndOffsetComputer.getSize_T(), integerConstant);
		final Expression offsetPlus = m_ExpressionTranslation.constructArithmeticExpression(
				loc, IASTBinaryExpression.op_plus, 
				offset, m_TypeSizeAndOffsetComputer.getSize_T(), 
				addition, m_TypeSizeAndOffsetComputer.getSize_T());
		return constructPointerFromBaseAndOffset(base, offsetPlus, loc);
	}

	private Expression constructOneDimensionalArrayAccess(final ILocation loc, Expression arr, Expression index) {
		Expression[] singletonIndex = new Expression[] { index };
		return new ArrayAccessExpression(loc, arr, singletonIndex);
	}
	
	private Expression constructOneDimensionalArrayStore(final ILocation loc, Expression arr, Expression index, Expression newValue) {
		Expression[] singletonIndex = new Expression[] { index };
		return new ArrayStoreExpression(loc, arr, singletonIndex, newValue);
	}

	// ensures #memory_X == old(#memory_X)[#ptr := #value];
	private EnsuresSpecification ensuresHeapArrayUpdate(final ILocation loc, 
			final String valueId, Function<Expression, Expression> valueModification, final String ptrId, 
			Function<Expression, Expression> ptrModification, final HeapDataArray hda) {
		final Expression valueExpr = new IdentifierExpression(loc, valueId);
        final Expression memArray = new IdentifierExpression(loc, hda.getVariableName());
        final Expression ptrExpr = new IdentifierExpression(loc, ptrId);
		return ensuresArrayUpdate(loc, valueModification.apply(valueExpr), ptrModification.apply(ptrExpr), memArray);
	}
	
	//#memory_$Pointer$ == old(#memory_X)[#ptr := #memory_X[#ptr]];
	private EnsuresSpecification ensuresHeapArrayHardlyModified(final ILocation loc, 
			final String ptrId, Function<Expression, Expression> ptrModification, final HeapDataArray hda) {
        final Expression memArray = new IdentifierExpression(loc, hda.getVariableName());
        final Expression ptrExpr = new IdentifierExpression(loc, ptrId);
        final Expression aae = constructOneDimensionalArrayAccess(loc, memArray, ptrExpr);
		return ensuresArrayUpdate(loc, aae, ptrModification.apply(ptrExpr), memArray);
	}
	
	
	
	private EnsuresSpecification ensuresArrayUpdate(final ILocation loc, 
			final Expression newValue, final Expression index, final Expression arrayExpr) {
		final Expression oldArray = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
        final Expression ase = constructOneDimensionalArrayStore(loc, oldArray, index, newValue);
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
					final ILocation loc, final Collection<T> vars, final Function<T, String> varToString) {
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
	private void addPointerBaseValidityCheck(final ILocation loc, 
			final String ptrName,
			final ArrayList<Specification> specList) {
		if (m_PointerBaseValidity == POINTER_CHECKMODE.IGNORE) {
			// add nothing
			return;
		} else {
			final Expression ptrExpr = new IdentifierExpression(loc, ptrName);
			final Expression ptrBase = getPointerBaseAddress(ptrExpr, loc);
			final ArrayAccessExpression aae = new ArrayAccessExpression(loc, 
					getValidArray(loc), new Expression[]{ ptrBase });
			final Expression isValid = m_BooleanArrayHelper.compareWithTrue(aae);
			final boolean isFreeRequires;
			if (m_PointerBaseValidity == POINTER_CHECKMODE.ASSERTandASSUME) {
		    	isFreeRequires = false;
			} else {
				assert m_PointerBaseValidity == POINTER_CHECKMODE.ASSUME;
				isFreeRequires = true;
			}
			final RequiresSpecification spec = 
					new RequiresSpecification(loc, isFreeRequires, isValid);
			final Check check = new Check(Spec.MEMORY_DEREFERENCE);
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
        final Expression addrIsValid = m_BooleanArrayHelper.compareWithTrue(
        		new ArrayAccessExpression(tuLoc, valid, idcFree));
        RequiresSpecification baseValid = new RequiresSpecification(tuLoc, free,
        		ExpressionFactory.newBinaryExpression(tuLoc, Operator.LOGICOR,
        				isNullPtr, addrIsValid));

        check.addToNodeAnnot(baseValid);
        specFree.add(baseValid);

        //ensures (if ~addr!base == 0 then #valid == old(#valid) else #valid == old(#valid)[~addr!base := false])
        Expression bLFalse = m_BooleanArrayHelper.constructFalse();
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
        				new String[] { ADDR }, m_TypeHandler.constructPointerType(tuLoc)) }, new VarList[0],
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
        					new String[] { ADDR }, m_TypeHandler.constructPointerType(tuLoc)) }, new VarList[0],
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
        Expression bLFalse = m_BooleanArrayHelper.constructFalse();
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
        				new String[] { ADDR }, m_TypeHandler.constructPointerType(tuLoc)) }, new VarList[0],
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
        Expression base = new StructAccessExpression(
                tuLoc, res, SFO.POINTER_BASE);
        Expression[] idcMalloc = new Expression[] { base };
        Expression bLTrue = m_BooleanArrayHelper.constructTrue();
        Expression bLFalse = m_BooleanArrayHelper.constructFalse();
        IdentifierExpression size = new IdentifierExpression(tuLoc, SIZE);
        List<Specification> specMalloc = new ArrayList<Specification>();

        specMalloc.add(new EnsuresSpecification(tuLoc, false,
                ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
                        new ArrayAccessExpression(tuLoc, ExpressionFactory.newUnaryExpression(
                                tuLoc, UnaryExpression.Operator.OLD, valid),
                                idcMalloc), bLFalse)));
        specMalloc.add(ensuresArrayUpdate(tuLoc, bLTrue, base, valid));
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
        decl.add(new Procedure(tuLoc, new Attribute[0], MemoryModelDeclarations.Ultimate_Alloc.getName(),
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
        	decl.add(new Procedure(tuLoc, new Attribute[0], MemoryModelDeclarations.Ultimate_Alloc.getName(),
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
//    
//    /**
//     * Creates a function call expression for the ~malloc(size) function!
//     * 
//     * @param main
//     *            a reference to the main dispatcher.
//     * @param fh
//     *            a reference to the FunctionHandler - required to add
//     *            information to the call graph.
//     * @param size
//     *            the expression referring to size of the memory to be
//     *            allocated.
//     * @param loc
//     *            Location for errors and new nodes in the AST.
//     * @return a function call expression for ~malloc(size).
//     */
//    public ExpressionResult getMallocCall(Dispatcher main, FunctionHandler fh,
//            Expression size, ILocation loc) {
//    	CPointer voidPointer = new CPointer(new CPrimitive(PRIMITIVE.VOID));
//    	String tmpId = m_NameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, voidPointer);
//        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, m_TypeHandler.constructPointerType(loc), loc);
//        
//        LocalLValue llVal = new LocalLValue(new VariableLHS(loc, tmpId), voidPointer);
//        ExpressionResult mallocRex = new ExpressionResult(llVal);
//        
//        mallocRex.stmt.add(getMallocCall(main, fh, size, llVal, loc));
//        mallocRex.auxVars.put(tVarDecl, loc);
//        mallocRex.decl.add(tVarDecl);
//        
//		assert (CHandler.isAuxVarMapcomplete(main, mallocRex.decl, mallocRex.auxVars));
//		return mallocRex;
//    }

    public CallStatement getMallocCall(Dispatcher main,	FunctionHandler fh, 
			LocalLValue resultPointer, ILocation loc) {
    	return getMallocCall(calculateSizeOf(loc, resultPointer.getCType()), 
    			((VariableLHS) resultPointer.getLHS()).getIdentifier(), loc);
    }

    public CallStatement getMallocCall(Expression size,
			String resultVarId, ILocation loc) {
    	m_RequiredMemoryModelFeatures.require(MemoryModelDeclarations.Ultimate_Alloc);
        CallStatement result = new CallStatement(loc, false, 
        		new VariableLHS[] { new VariableLHS(loc, resultVarId) }, MemoryModelDeclarations.Ultimate_Alloc.getName(), new Expression[] { size });
        
        // add required information to function handler.
        if (m_FunctionHandler.getCurrentProcedureID() != null) {
            LinkedHashSet<String> mgM = new LinkedHashSet<String>();
            mgM.add(SFO.VALID);
            mgM.add(SFO.LENGTH);
            if (!m_FunctionHandler.getModifiedGlobals().containsKey(MemoryModelDeclarations.Ultimate_Alloc.getName())) {
            	m_FunctionHandler.getModifiedGlobals().put(MemoryModelDeclarations.Ultimate_Alloc.getName(), mgM);
            	m_FunctionHandler.getCallGraph().put(MemoryModelDeclarations.Ultimate_Alloc.getName(), new LinkedHashSet<String>());
            }
            m_FunctionHandler.getCallGraph().get(m_FunctionHandler.getCurrentProcedureID()).add(MemoryModelDeclarations.Ultimate_Alloc.getName());
        }
        return result;
    }
    
    /**
     * Generates a call of the read procedure and writes the returned value to a
     * temp variable, returned in the expression of the returned
     * ResultExpression.
     * Note that we only read simple types from the heap -- when reading e.g. an  
     * array, we have to make readCalls for each cell.
     * @param tPointer
     *            the address to read from.
     * @param pointerCType
     *            the CType of the pointer in tPointer
     * 
     * @return all declarations and statements required to perform the read,
     *         plus an identifierExpression holding the read value.
     */
    // 2015-10
    public ExpressionResult getReadCall(Expression address, CType resultType) {
    	ILocation loc = address.getLocation();
//    	if (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
//    			&& (resultType.getUnderlyingType() instanceof CPrimitive)) {
//    		CPrimitive cPrimitive = (CPrimitive) resultType.getUnderlyingType();
//    		if (main.getTypeSizes().getSize(cPrimitive.getType()) > 
//    				main.getTypeSizes().getSize(PRIMITIVE.INT)) {
//    			throw new UnsupportedSyntaxException(loc, 
//    					"cannot read " + cPrimitive + " from heap"); 
//    		}
//    	}
//		boolean bitvectorConversionNeeded = (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
//    			&& (resultType.getUnderlyingType() instanceof CPrimitive)
//    			&& main.getTypeSizes().getSize(((CPrimitive) resultType.getUnderlyingType()).getType()) < 
//				main.getTypeSizes().getSize(PRIMITIVE.INT));
    	boolean bitvectorConversionNeeded = false;
    	
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
        
        
        final String readCallProcedureName;
        {
        	
        	final CType ut;
        	if (resultType instanceof CNamed) {
        		ut = ((CNamed) resultType).getUnderlyingType();
        	} else {
        		ut = resultType;
        	}
        	
        	if (ut instanceof CPrimitive) {
    			CPrimitive cp = (CPrimitive) ut;
    			m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(cp.getType());
    			readCallProcedureName = m_MemoryModel.getReadProcedureName(cp.getType());
    		} else if (ut instanceof CPointer) {
    			m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
    			readCallProcedureName = m_MemoryModel.getReadPointerProcedureName();
    		} else if (ut instanceof CNamed) {
    			throw new AssertionError("we took underlying type");
    		} else if (ut instanceof CArray) {
    			// we assume it is an Array on Heap
//    			assert main.cHandler.isHeapVar(((IdentifierExpression) lrVal.getValue()).getIdentifier());
    			//but it may not only be on heap, because it is addressoffed, but also because it is inside
    			// a struct that is addressoffed..
    			m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
    			readCallProcedureName = m_MemoryModel.getReadPointerProcedureName();
    		} else if (ut instanceof CEnum) {
    			//enum is treated like an int
    			m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(PRIMITIVE.INT);
    			readCallProcedureName = m_MemoryModel.getReadProcedureName(PRIMITIVE.INT);
    		} else {
    			throw new UnsupportedOperationException("unsupported type " + ut);
    		}
        }
        
        String tmpId = m_NameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD, resultType);
        final ASTType tmpAstType;
        if (bitvectorConversionNeeded) {
        	tmpAstType = m_TypeHandler.ctype2asttype(loc, resultType);
        } else {
        	tmpAstType = m_TypeHandler.ctype2asttype(loc, resultType);
        }
        VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpId, tmpAstType, loc);
        auxVars.put(tVarDecl, loc);
        decl.add(tVarDecl);
        VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, tmpId) };
        CallStatement call = new CallStatement(loc, false, lhs, readCallProcedureName,//heapType.toString(),
                new Expression[] { address, calculateSizeOf(loc, resultType) });
        for (Overapprox overapprItem : overappr) {
            call.getPayload().getAnnotations().put(Overapprox.getIdentifier(),
                    overapprItem);
        }
        stmt.add(call);
		assert (CHandler.isAuxVarMapcomplete(m_NameHandler, decl, auxVars));
		
		ExpressionResult result; 
		if (bitvectorConversionNeeded) {
			result = new ExpressionResult(stmt, 
	        		new RValue(new IdentifierExpression(loc, tmpId), resultType),
	        		decl, auxVars, overappr);
			m_ExpressionTranslation.convertIntToInt(loc, result, (CPrimitive) resultType.getUnderlyingType());
	        String bvtmpId = m_NameHandler.getTempVarUID(SFO.AUXVAR.MEMREAD, resultType);
	        VariableDeclaration bvtVarDecl = SFO.getTempVarVariableDeclaration(bvtmpId, tmpAstType, loc);
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
    
    
    /**
     * Generates a procedure call to writeT(val, ptr), writing val to the
     * according memory array.
     * (for the C-methode the argument order is value, target, for this
     * method it's the other way around)
     * @param hlv
     *            the HeapLvalue containing the address to write to
     * @param rval
     *            the value to write.
     * 
     * @return the required Statements to perform the write.
     */
    public ArrayList<Statement> getWriteCall(ILocation loc, HeapLValue hlv, Expression value, 
    		CType valueType) {
//    	if (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
//    			&& (valueType.getUnderlyingType() instanceof CPrimitive)) {
//    		CPrimitive cPrimitive = (CPrimitive) valueType.getUnderlyingType();
//    		if (main.getTypeSizes().getSize(cPrimitive.getType()) > 
//    				main.getTypeSizes().getSize(PRIMITIVE.INT)) {
//    			throw new UnsupportedSyntaxException(loc, 
//    					"cannot write " + cPrimitive + " to heap"); 
//    		}
//    	}
//		boolean bitvectorConversionNeeded = (((CHandler) main.cHandler).getExpressionTranslation() instanceof BitvectorTranslation
//    			&& (valueType.getUnderlyingType() instanceof CPrimitive)
//    			&& main.getTypeSizes().getSize(((CPrimitive) valueType.getUnderlyingType()).getType()) < 
//				main.getTypeSizes().getSize(PRIMITIVE.INT));
//		if (bitvectorConversionNeeded) {
//			RValue tmpworkaroundrvalue = new RValue(value, valueType.getUnderlyingType(), false, false);
//			ExpressionResult tmpworkaround = new ExpressionResult(tmpworkaroundrvalue);
//			m_ExpressionTranslation.convertIntToInt(loc, tmpworkaround, new CPrimitive(PRIMITIVE.INT));
//			value = tmpworkaround.lrVal.getValue();
//			valueType = tmpworkaround.lrVal.getCType();
//		}
		
        ArrayList<Statement> stmt = new ArrayList<Statement>();
        
        
        if (valueType instanceof CNamed)
        	valueType = ((CNamed) valueType).getUnderlyingType();
        
        if (valueType instanceof CPrimitive) {
        	CPrimitive cp = (CPrimitive) valueType;
        	m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(cp.getType());
        	String writeCallProcedureName = m_MemoryModel.getWriteProcedureName(cp.getType());
        	HeapDataArray dhp = m_MemoryModel.getDataHeapArray(cp.getType());
    		m_FunctionHandler.getModifiedGlobals().
				get(m_FunctionHandler.getCurrentProcedureID()).add(dhp.getVariableName());
    		stmt.add(new CallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
    				new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType())}));
        } else if (valueType instanceof CEnum) {
        	//treat like INT
        	m_RequiredMemoryModelFeatures.reportDataOnHeapRequired(PRIMITIVE.INT);
        	String writeCallProcedureName = m_MemoryModel.getWriteProcedureName(PRIMITIVE.INT);
        	HeapDataArray dhp = m_MemoryModel.getDataHeapArray(PRIMITIVE.INT);
    		m_FunctionHandler.getModifiedGlobals().
				get(m_FunctionHandler.getCurrentProcedureID()).add(dhp.getVariableName());
    		stmt.add(new CallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
    				new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType())}));
        } else if (valueType instanceof CPointer) {
        	m_RequiredMemoryModelFeatures.reportPointerOnHeapRequired();
        	String writeCallProcedureName = m_MemoryModel.getWritePointerProcedureName();
        	HeapDataArray dhp = m_MemoryModel.getPointerHeapArray();
    		m_FunctionHandler.getModifiedGlobals().
				get(m_FunctionHandler.getCurrentProcedureID()).add(dhp.getVariableName());
    		stmt.add(new CallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
    				new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType())}));
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
        		stmt.addAll(getWriteCall(loc, fieldHlv, sae, fieldType));
        	}
        	
        } else if (valueType instanceof CArray) {
        	
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
						stmt.addAll(getWriteCall(loc, new HeapLValue(constructPointerFromBaseAndOffset(newStartAddressBase, arrayEntryAddressOffset, loc), arrayType.getValueType()), 
								arrayAccRVal.getValue(), 
								arrayAccRVal.getCType()));
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
		for (LocalLValueILocationPair llvp : variablesToBeMalloced.currentScopeKeys()) 
			mallocs.add(this.getMallocCall(main, m_FunctionHandler, 
					llvp.llv, llvp.loc));
		ArrayList<Statement> frees = new ArrayList<Statement>();
		for (LocalLValueILocationPair llvp : variablesToBeFreed.currentScopeKeys()) {  //frees are inserted in handleReturnStm
			frees.add(getDeallocCall(main, m_FunctionHandler, llvp.llv, llvp.loc));
			frees.add(new HavocStatement(llvp.loc, new VariableLHS[] { (VariableLHS) llvp.llv.getLHS() }));
		}
		ArrayList<Statement> newBlockAL = new ArrayList<Statement>();
		newBlockAL.addAll(mallocs);
		newBlockAL.addAll(block);
		newBlockAL.addAll(frees);
		return newBlockAL;
	}
	
	public void addVariableToBeFreed(Dispatcher main, LocalLValueILocationPair llvp) {
		variablesToBeFreed.put(llvp, variablesToBeFreed.getActiveScopeNum());
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
	
	public IBooleanArrayHelper getBooleanArrayHelper() {
		return m_BooleanArrayHelper;
	}

	/**
	 * Add or subtract a Pointer and an integer.
	 * Use this method only if you are sure that the type of the integer
	 * is the same as the type that we use for our pointer components.
	 * Otherwise, use the method below.
	 * @param operator Either plus or minus.
	 * @param integer
	 * @param valueType
	 *            The value type the pointer points to (we need it because we
	 *            have to multiply with its size)
	 * 
	 * @return a pointer of the form: {base: ptr.base, offset: ptr.offset +
	 *         integer * sizeof(valueType)}
	 */
	public Expression doPointerArithmetic(int operator, ILocation loc, Expression ptrAddress, RValue integer,
			CType valueType) {
		if (m_TypeSizes.getSize(((CPrimitive) integer.getCType()).getType()) != 
				m_TypeSizes.getSize(m_ExpressionTranslation.getCTypeOfPointerComponents().getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}
		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);
		final Expression timesSizeOf = multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(), 
					m_ExpressionTranslation.getCTypeOfPointerComponents());
		final Expression sum = m_ExpressionTranslation.constructArithmeticExpression(loc, 
				operator, pointerOffset,
				m_ExpressionTranslation.getCTypeOfPointerComponents(), timesSizeOf, m_ExpressionTranslation.getCTypeOfPointerComponents());
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
		return newPointer;
	}
	
	
	/**
	 * Multiply an integerExpresion with the size of another type.
	 * @param integerExpresionType {@link CType} whose translation is the Boogie 
	 * 		type of integerExpression and the result.
	 * @return An {@link Expression} that represents <i>integerExpression * sizeof(valueType)</i>
	 */
	public Expression multiplyWithSizeOfAnotherType(ILocation loc, CType valueType, Expression integerExpression,
			CPrimitive integerExpresionType) {
		final Expression timesSizeOf;
		timesSizeOf = m_ExpressionTranslation.constructArithmeticExpression(
				loc, IASTBinaryExpression.op_multiply, integerExpression,
				integerExpresionType, calculateSizeOf(loc, valueType), integerExpresionType);
		return timesSizeOf;
	}
	
	
	
	public interface IBooleanArrayHelper {
		public ASTType constructBoolReplacementType();
		public Expression constructTrue();
		public Expression constructFalse();
		public Expression compareWithTrue(Expression expr);
	}
	
	public class BooleanArrayHelper_Bool implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, "bool");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new BooleanLiteral(ignoreLoc, true);
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new BooleanLiteral(ignoreLoc, false);
		}

		@Override
		public Expression compareWithTrue(Expression expr) {
			return expr;
		}
		
	}
	
	public class BooleanArrayHelper_Integer implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, "int");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new IntegerLiteral(ignoreLoc, "1");
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new IntegerLiteral(ignoreLoc, "0");
		}

		@Override
		public Expression compareWithTrue(Expression expr) {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.newBinaryExpression(
					ignoreLoc, Operator.COMPEQ, expr, constructTrue());
		}
		
	}
	
	public class BooleanArrayHelper_Bitvector implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, "bv1");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new BitvecLiteral(ignoreLoc, "1", 1);
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new BitvecLiteral(ignoreLoc, "0", 1);
		}

		@Override
		public Expression compareWithTrue(Expression expr) {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.newBinaryExpression(
					ignoreLoc, Operator.COMPEQ, expr, constructTrue());
		}
		
	}
	
	

}
