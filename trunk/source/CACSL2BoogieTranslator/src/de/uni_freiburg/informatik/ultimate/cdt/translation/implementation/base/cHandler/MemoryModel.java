/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * Instances of this class define a memory model.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MemoryModel {
	
	protected final static String s_ReadProcedurePrefix = "read~";
	protected final static String s_WriteProcedurePrefix = "write~";
	private final int m_MemoryModelResolution;
	
	protected final TypeSizes m_TypeSizes;
	
	private final HeapDataArray m_IntegerArray;
	private final HeapDataArray m_FloatingArray;
	private final HeapDataArray m_PointerArray;
	
	public MemoryModel(int memoryModelResolution, TypeSizes typeSizes, ITypeHandler typeHandler, AExpressionTranslation expressionTranslation) {
		m_MemoryModelResolution = memoryModelResolution;
		m_TypeSizes = typeSizes;
		

		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		/*
		 * In our Lindenmann-Hoenicke memory model, we use an array for all
		 * integer data on the heap. This method returns the CType that we use to
		 * represents this data.
		 */
        ASTType intArrayType = typeHandler.ctype2asttype(ignoreLoc, 
        		new CPrimitive(PRIMITIVE.INT));
        
    	/*
    	 * In our Lindenmann-Hoenicke memory model, we use an array for all
    	 * floating type data on the heap. This method returns the CType that we 
    	 * use to represent this data.
    	 */
        ASTType realArrayType = typeHandler.ctype2asttype(ignoreLoc, 
        		new CPrimitive(PRIMITIVE.FLOAT));
        
       	m_IntegerArray = new HeapDataArray(SFO.INT, intArrayType, 0);
       	m_FloatingArray = new HeapDataArray(SFO.REAL, realArrayType, 0);
       	m_PointerArray = new HeapDataArray(SFO.POINTER, typeHandler.constructPointerType(ignoreLoc), 0);
	}
       	
	public int getMemoryModelResolution() {
		return m_MemoryModelResolution;
	}
	
	public String getReadProcedureName(PRIMITIVE primitive) {
		final HeapDataArray hda = getDataHeapArray(primitive);
		final String result;
		if (getMemoryModelResolution() == 0) {
			result = s_ReadProcedurePrefix + hda.getName();
		} else {
			int size = m_TypeSizes.getSize(primitive);
			result = s_ReadProcedurePrefix + hda.getName() + size;
		}
		return result;
	}


	public String getWriteProcedureName(PRIMITIVE primitive) {
		final HeapDataArray hda = getDataHeapArray(primitive);
		final String result;
		if (getMemoryModelResolution() == 0) {
			result = s_WriteProcedurePrefix + hda.getName();
		} else {
			int size = m_TypeSizes.getSize(primitive);
			result = s_WriteProcedurePrefix + hda.getName() + size;
		}
		return result;
	}
	
	public String getReadPointerProcedureName() {
		final HeapDataArray hda = m_PointerArray;
		final String result;
		if (getMemoryModelResolution() == 0) {
			result = s_ReadProcedurePrefix + hda.getName();
		} else {
			int size = m_TypeSizes.getSizeOfPointer();
			result = s_ReadProcedurePrefix + hda.getName() + size;
		}
		return result;
	}


	public String getWritePointerProcedureName() {
		final HeapDataArray hda = m_PointerArray;
		final String result;
		if (getMemoryModelResolution() == 0) {
			result = s_WriteProcedurePrefix + hda.getName();
		} else {
			int size = m_TypeSizes.getSizeOfPointer();
			result = s_WriteProcedurePrefix + hda.getName() + size;
		}
		return result;
	}

	
	public HeapDataArray getDataHeapArray(PRIMITIVE primitive) {
		if (primitive.isIntegertype()) {
			return m_IntegerArray;
		} else if(primitive.isFloatingtype()) {
			return m_FloatingArray;
		} else {
			throw new AssertionError();
		}
	}
	
	public HeapDataArray getPointerHeapArray() {
		return m_PointerArray;
	}

	public ArrayList<HeapDataArray> getDataHeapArrays(RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		ArrayList<HeapDataArray> result = new ArrayList<>();
		if (requiredMemoryModelFeatures.isPointerOnHeapRequired()) {
			result.add(getPointerHeapArray());
		}
		for (PRIMITIVE primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			result.add(getDataHeapArray(primitive));
		}
		return result;
	}

}
