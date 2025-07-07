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
 * Instances of this class define a Memory Structure.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MemoryStructure_SingleBitprecise extends BaseMemoryStructure {

	private final HeapDataArray mDataArray;
	private final int mResolution;

	public MemoryStructure_SingleBitprecise(final int memoryStructureResolution, final TypeSizes typeSizes,
			final ITypeHandler typeHandler) {
		super(typeSizes, typeHandler);

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final ASTType intArrayType =
				typeHandler.byteSize2AstType(ignoreLoc, CPrimitiveCategory.INTTYPE, memoryStructureResolution);
		final BoogieType boogieType = mTypeHandler.getBoogieTypeForBoogieASTType(intArrayType);

		mResolution = memoryStructureResolution;
		mDataArray = new HeapDataArray(SFO.INT, intArrayType, boogieType, mTypeHandler.getBoogiePointerType(),
				memoryStructureResolution);
	}

	@Override
	public String getProcedureSuffix(final CPrimitives primitive) {
		return mDataArray.getName() + primitive.getPrimitiveCategory() + mTypeSizes.getSize(primitive);
	}

	@Override
	public HeapDataArray getDataHeapArray(final CPrimitives primitive) {
		return mDataArray;
	}

	@Override
	public List<ReadWriteDefinition> getReadWriteDefinitionForNonPointerHeapDataArray(final HeapDataArray hda,
			final RequiredMemoryModelFeatures requiredMemoryStructureFeatures) {
		final HashRelation3<CPrimitiveCategory, Integer, CPrimitives> bytesizes2primitives = new HashRelation3<>();
		for (final CPrimitives primitive : requiredMemoryStructureFeatures.getDataOnHeapRequired()) {
			final int bytesize = mTypeSizes.getSize(primitive);
			if (getDataHeapArray(primitive) == hda) {
				bytesizes2primitives.addTriple(primitive.getPrimitiveCategory(), bytesize, primitive);
			}
		}
		final List<ReadWriteDefinition> result = new ArrayList<>();
		for (final CPrimitiveCategory cPrimitiveCategory : bytesizes2primitives.projectToFst()) {
			for (final Integer bytesize : bytesizes2primitives.projectToSnd(cPrimitiveCategory)) {
				final Set<CPrimitives> primitives = bytesizes2primitives.projectToTrd(cPrimitiveCategory, bytesize);
				final CPrimitives representative = primitives.iterator().next();
				final String procedureName = getProcedureSuffix(representative);
				final ASTType astType = mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(),
						new CPrimitive(representative));
				final boolean alsoUncheckedWrite = DataStructureUtils.haveNonEmptyIntersection(
						requiredMemoryStructureFeatures.getUncheckedWriteRequired(), primitives);
				final boolean alsoInit = DataStructureUtils
						.haveNonEmptyIntersection(requiredMemoryStructureFeatures.getInitWriteRequired(), primitives);
				result.add(new ReadWriteDefinition(procedureName, bytesize, astType, new CPrimitive(representative),
						alsoUncheckedWrite, alsoInit));
			}
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
