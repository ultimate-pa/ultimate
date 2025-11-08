package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryStructureBase.ReadWriteDefinition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * The interface defining the functions for the different memory structures.
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
