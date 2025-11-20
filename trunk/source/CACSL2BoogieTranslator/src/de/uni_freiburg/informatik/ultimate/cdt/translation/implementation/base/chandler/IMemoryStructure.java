/*
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryStructureBase.ReadWriteDefinition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * The interface defining the functions for the different memory structures.
 *
 * @author Jan Körner
 */
public interface IMemoryStructure {
	String getReadProcedureName(final CPrimitives primitive);

	String getUncheckedReadProcedureName(final CPrimitives primitive);

	String getWriteProcedureName(final CPrimitives primitive);

	String getUncheckedWriteProcedureName(final CPrimitives primitive);

	String getInitWriteProcedureName(final CPrimitives primitive);

	String getReadPointerProcedureName();

	String getUncheckedReadPointerProcedureName();

	String getWritePointerProcedureName();

	String getUncheckedWritePointerProcedureName();

	String getInitPointerProcedureName();

	HeapDataArray getDataHeapArray(CPrimitives primitive);

	HeapDataArray getPointerHeapArray();

	Collection<HeapDataArray> getDataHeapArrays(final RequiredMemoryModelFeatures requiredMemoryStructureFeatures);

	List<ReadWriteDefinition> getReadWriteDefinitionForHeapDataArray(final HeapDataArray hda,
			final RequiredMemoryModelFeatures requiredMemoryStructureFeatures);
}
