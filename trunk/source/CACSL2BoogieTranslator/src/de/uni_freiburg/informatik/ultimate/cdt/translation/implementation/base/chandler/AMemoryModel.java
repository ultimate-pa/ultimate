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

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public abstract class AMemoryModel {
	
	protected final static String s_ReadProcedurePrefix = "read~";
	protected final static String s_WriteProcedurePrefix = "write~";
	
	protected final ITypeHandler mTypeHandler;
	protected final TypeSizes mTypeSizes;
	
	private final HeapDataArray mPointerArray;
	
	public AMemoryModel(final TypeSizes typeSizes, final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
       	mPointerArray = new HeapDataArray(SFO.POINTER, typeHandler.constructPointerType(ignoreLoc), bytesizeOfStoredPointerComponents());
	}
	
	protected abstract int bytesizeOfStoredPointerComponents();
	
	protected abstract String getProcedureSuffix(CPrimitives primitive);
       	
	public final String getReadProcedureName(final CPrimitives primitive) {
		return s_ReadProcedurePrefix + getProcedureSuffix(primitive);
	}

	public final String getWriteProcedureName(final CPrimitives primitive) {
		return s_WriteProcedurePrefix + getProcedureSuffix(primitive);
	}
	
	public final String getReadPointerProcedureName() {
		final HeapDataArray hda = mPointerArray;
		return s_ReadProcedurePrefix + hda.getName();
	}


	public final String getWritePointerProcedureName() {
		final HeapDataArray hda = mPointerArray;
		return s_WriteProcedurePrefix + hda.getName();
	}

	
	public abstract HeapDataArray getDataHeapArray(CPrimitives primitive);
	
	public final HeapDataArray getPointerHeapArray() {
		return mPointerArray;
	}

	public final Collection<HeapDataArray> getDataHeapArrays(final RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		final Set<HeapDataArray> result = new HashSet<>();
		if (requiredMemoryModelFeatures.isPointerOnHeapRequired()) {
			result.add(getPointerHeapArray());
		}
		for (final CPrimitives primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			result.add(getDataHeapArray(primitive));
		}
		return result;
	}
	
	public final List<ReadWriteDefinition> getReadWriteDefinitionForHeapDataArray(final HeapDataArray hda, final RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		if (hda == mPointerArray) {
			if (requiredMemoryModelFeatures.isPointerOnHeapRequired()) {
				return Collections.singletonList(new ReadWriteDefinition(
						getPointerHeapArray().getName(), bytesizeOfStoredPointerComponents(), getPointerHeapArray().getASTType(), Collections.emptySet()));
			} else {
				return Collections.emptyList();
			}
		} else {
			return getReadWriteDefinitionForNonPointerHeapDataArray(hda, requiredMemoryModelFeatures);
		}
	}
	
	protected abstract List<ReadWriteDefinition> getReadWriteDefinitionForNonPointerHeapDataArray(HeapDataArray hda,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures);
	
	public class ReadWriteDefinition {
		private final String mProcedureSuffix;
		private final int mBytesize;
		private final ASTType mASTType;
		private final Set<CPrimitives> mPrimitives;
		private final Set<CPrimitiveCategory> mCPrimitiveCategory;
		public ReadWriteDefinition(final String procedureName, final int bytesize, final ASTType aSTType, final Set<CPrimitives> primitives) {
			super();
			mProcedureSuffix = procedureName;
			mBytesize = bytesize;
			mASTType = aSTType;
			mPrimitives = primitives;
			final Function<CPrimitives, CPrimitiveCategory> mapper = (x -> x.getPrimitiveCategory());
			mCPrimitiveCategory = primitives.stream().map(mapper).collect(Collectors.toSet());
		}
		public String getReadProcedureName() {
			return s_ReadProcedurePrefix + mProcedureSuffix;
		}
		public String getWriteProcedureName() {
			return s_WriteProcedurePrefix + mProcedureSuffix;
		}
		public int getBytesize() {
			return mBytesize;
		}
		public ASTType getASTType() {
			return mASTType;
		}
		public Set<CPrimitives> getPrimitives() {
			return mPrimitives;
		}
		public Set<CPrimitiveCategory> getCPrimitiveCategory() {
			return mCPrimitiveCategory;
		}
		@Override
		public String toString() {
			return "ReadWriteDefinition [mProcedureSuffix=" + mProcedureSuffix + ", mBytesize=" + mBytesize
					+ ", mASTType=" + mASTType + ", mPrimitives=" + mPrimitives + "]";
		}
	}

}
