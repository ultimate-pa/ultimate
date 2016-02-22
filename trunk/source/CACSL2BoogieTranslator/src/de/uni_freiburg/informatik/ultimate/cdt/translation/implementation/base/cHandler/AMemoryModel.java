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

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.AMemoryModel.ReadWriteDefinition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public abstract class AMemoryModel {
	
	protected final static String s_ReadProcedurePrefix = "read~";
	protected final static String s_WriteProcedurePrefix = "write~";
	
	protected final ITypeHandler m_TypeHandler;
	protected final TypeSizes m_TypeSizes;
	
	private final HeapDataArray m_PointerArray;
	
	public AMemoryModel(TypeSizes typeSizes, ITypeHandler typeHandler, AExpressionTranslation expressionTranslation) {
		m_TypeSizes = typeSizes;
		m_TypeHandler = typeHandler;
		ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
       	m_PointerArray = new HeapDataArray(SFO.POINTER, typeHandler.constructPointerType(ignoreLoc), bytesizeOfStoredPointerComponents());
	}
	
	protected abstract int bytesizeOfStoredPointerComponents();
	
	protected abstract String getProcedureSuffix(PRIMITIVE primitive);
       	
	public final String getReadProcedureName(PRIMITIVE primitive) {
		return s_ReadProcedurePrefix + getProcedureSuffix(primitive);
	}

	public final String getWriteProcedureName(PRIMITIVE primitive) {
		return s_WriteProcedurePrefix + getProcedureSuffix(primitive);
	}
	
	public final String getReadPointerProcedureName() {
		final HeapDataArray hda = m_PointerArray;
		return s_ReadProcedurePrefix + hda.getName();
	}


	public final String getWritePointerProcedureName() {
		final HeapDataArray hda = m_PointerArray;
		return s_WriteProcedurePrefix + hda.getName();
	}

	
	public abstract HeapDataArray getDataHeapArray(PRIMITIVE primitive);
	
	public final HeapDataArray getPointerHeapArray() {
		return m_PointerArray;
	}

	public final Collection<HeapDataArray> getDataHeapArrays(RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		Set<HeapDataArray> result = new HashSet<>();
		if (requiredMemoryModelFeatures.isPointerOnHeapRequired()) {
			result.add(getPointerHeapArray());
		}
		for (PRIMITIVE primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			result.add(getDataHeapArray(primitive));
		}
		return result;
	}
	
	public final List<ReadWriteDefinition> getBytesizesStoredInHeapDataArray(HeapDataArray hda, RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		if (hda == m_PointerArray) {
			if (requiredMemoryModelFeatures.isPointerOnHeapRequired()) {
				return Collections.singletonList(new ReadWriteDefinition(
						getPointerHeapArray().getName(), bytesizeOfStoredPointerComponents(), getPointerHeapArray().getASTType(), null));
			} else {
				return Collections.emptyList();
			}
		} else {
			return getBytesizesStoredInNonPointerHeapDataArray(hda, requiredMemoryModelFeatures);
		}
	}
	
	protected abstract List<ReadWriteDefinition> getBytesizesStoredInNonPointerHeapDataArray(HeapDataArray hda,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures);
	
	public class ReadWriteDefinition {
		private final String m_ProcedureSuffix;
		private final int m_Bytesize;
		private final ASTType m_ASTType;
		private final Set<PRIMITIVE> m_Primitives;
		public ReadWriteDefinition(String procedureName, int bytesize, ASTType aSTType, Set<PRIMITIVE> primitives) {
			super();
			m_ProcedureSuffix = procedureName;
			m_Bytesize = bytesize;
			m_ASTType = aSTType;
			m_Primitives = primitives;
		}
		public String getReadProcedureName() {
			return s_ReadProcedurePrefix + m_ProcedureSuffix;
		}
		public String getWriteProcedureName() {
			return s_WriteProcedurePrefix + m_ProcedureSuffix;
		}
		public int getBytesize() {
			return m_Bytesize;
		}
		public ASTType getASTType() {
			return m_ASTType;
		}
		public Set<PRIMITIVE> getPrimitives() {
			return m_Primitives;
		}
		@Override
		public String toString() {
			return "ReadWriteDefinition [m_ProcedureSuffix=" + m_ProcedureSuffix + ", m_Bytesize=" + m_Bytesize
					+ ", m_ASTType=" + m_ASTType + ", m_Primitives=" + m_Primitives + "]";
		}
	}

}
