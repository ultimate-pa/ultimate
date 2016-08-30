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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MemoryModel_SingleBitprecise extends AMemoryModel {
	
	private final HeapDataArray mDataArray;
	private final int mResolution;
	
	public MemoryModel_SingleBitprecise(int memoryModelResolution, TypeSizes typeSizes, TypeHandler typeHandler, AExpressionTranslation expressionTranslation) {
		super(typeSizes, typeHandler, expressionTranslation);
		
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final ASTType intArrayType = typeHandler.bytesize2asttype(ignoreLoc, CPrimitiveCategory.INTTYPE, memoryModelResolution);
		
        mResolution = memoryModelResolution;
		mDataArray = new HeapDataArray(SFO.INT, intArrayType, memoryModelResolution);
	}
       	
	@Override
	public String getProcedureSuffix(CPrimitives primitive) {
		if (primitive.isFloatingtype()) {
			throw new UnsupportedOperationException("Floating types are not yet supported in "
						+ this.getClass().getSimpleName());
		}
		return mDataArray.getName() + mTypeSizes.getSize(primitive);

	}


	@Override
	public HeapDataArray getDataHeapArray(CPrimitives primitive) {
		return mDataArray;
	}
	
	@Override
	public List<ReadWriteDefinition> getReadWriteDefinitionForNonPointerHeapDataArray(HeapDataArray hda, RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		final HashRelation<Integer, CPrimitives> bytesizes2primitives = new HashRelation<>();
		for (final CPrimitives primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			final int bytesize = mTypeSizes.getSize(primitive);
			if (getDataHeapArray(primitive) == hda) {
				bytesizes2primitives.addPair(bytesize, primitive);
			}
		}
		final List<ReadWriteDefinition> result = new ArrayList<>();
		for (final Integer bytesize : bytesizes2primitives.getDomain()) {
			final CPrimitives representative = bytesizes2primitives.getImage(bytesize).iterator().next();
			final String procedureName = getProcedureSuffix(representative);
			final ASTType astType = mTypeHandler.ctype2asttype(LocationFactory.createIgnoreCLocation(), new CPrimitive(representative));
			result.add(new ReadWriteDefinition(procedureName, bytesize, astType, bytesizes2primitives.getImage(bytesize)));
		}
		return result;
	}
	
	@Override
	protected int bytesizeOfStoredPointerComponents() {
		return mTypeSizes.getSizeOfPointer();
	}

	public int getResolution() {
		return mResolution;
	}


	

}
