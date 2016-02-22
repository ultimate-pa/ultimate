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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MemoryModel_Unbounded extends AMemoryModel {
	
	private final HeapDataArray m_IntegerArray;
	private final HeapDataArray m_FloatingArray;
	
	public MemoryModel_Unbounded(TypeSizes typeSizes, ITypeHandler typeHandler, AExpressionTranslation expressionTranslation) {
		super(typeSizes, typeHandler, expressionTranslation);
		
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
	}
	
	@Override
	public String getProcedureSuffix(PRIMITIVE primitive) {
		return getDataHeapArray(primitive).getName();
	}
       	
	@Override
	public HeapDataArray getDataHeapArray(PRIMITIVE primitive) {
		if (primitive.isIntegertype()) {
			return m_IntegerArray;
		} else if(primitive.isFloatingtype()) {
			return m_FloatingArray;
		} else {
			throw new AssertionError();
		}
	}
	

	
	@Override
	public List<ReadWriteDefinition> getBytesizesStoredInNonPointerHeapDataArray(HeapDataArray hda, RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		final HashRelation<Integer, PRIMITIVE> bytesizes2primitives = new HashRelation<>();
		for (PRIMITIVE primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			final int bytesize = 0;
			if (getDataHeapArray(primitive) == hda) {
				bytesizes2primitives.addPair(bytesize, primitive);
			}
		}
		List<ReadWriteDefinition> result = new ArrayList<>();
		for (Integer bytesize : bytesizes2primitives.getDomain()) {
			final PRIMITIVE representative = bytesizes2primitives.getImage(bytesize).iterator().next();
			final String procedureName = getProcedureSuffix(representative);
			final ASTType astType = m_TypeHandler.ctype2asttype(LocationFactory.createIgnoreCLocation(), new CPrimitive(representative));
			result.add(new ReadWriteDefinition(procedureName, bytesize, astType, bytesizes2primitives.getImage(bytesize)));
		}
		return result;
	}

	@Override
	protected int bytesizeOfStoredPointerComponents() {
		return 0;
	}



	
	

}
