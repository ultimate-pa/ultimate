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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MemoryModel_Unbounded extends BaseMemoryModel {

	private final HeapDataArray mIntegerArray;
	private final HeapDataArray mFloatingArray;

	public MemoryModel_Unbounded(final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final ExpressionTranslation expressionTranslation) {
		super(typeSizes, typeHandler, expressionTranslation);

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		/*
		 * In our Lindenmann-Hoenicke memory model, we use an array for all integer data on the heap. This method
		 * returns the CType that we use to represents this data.
		 */
		final ASTType intArrayType = typeHandler.cType2AstType(ignoreLoc, new CPrimitive(CPrimitives.INT));

		/*
		 * In our Lindenmann-Hoenicke memory model, we use an array for all floating type data on the heap. This method
		 * returns the CType that we use to represent this data.
		 */
		final ASTType realArrayType = typeHandler.cType2AstType(ignoreLoc, new CPrimitive(CPrimitives.FLOAT));

		final BoogieType boogieIntArrayType = mTypeHandler.getBoogieTypeForBoogieASTType(intArrayType);
		final BoogieType boogieRealArrayType = mTypeHandler.getBoogieTypeForBoogieASTType(realArrayType);

		mIntegerArray =
				new HeapDataArray(SFO.INT, intArrayType, boogieIntArrayType, mTypeHandler.getBoogiePointerType(), 0);
		mFloatingArray =
				new HeapDataArray(SFO.REAL, realArrayType, boogieRealArrayType, mTypeHandler.getBoogiePointerType(), 0);
	}

	@Override
	public String getProcedureSuffix(final CPrimitives primitive) {
		return getDataHeapArray(primitive).getName();
	}

	@Override
	public HeapDataArray getDataHeapArray(final CPrimitives primitive) {
		if (primitive.isIntegertype()) {
			return mIntegerArray;
		} else if (primitive.isFloatingtype()) {
			return mFloatingArray;
		} else {
			throw new AssertionError();
		}
	}

	@Override
	public List<ReadWriteDefinition> getReadWriteDefinitionForNonPointerHeapDataArray(final HeapDataArray hda,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures) {
		final HashRelation<Integer, CPrimitives> bytesizes2primitives = new HashRelation<>();
		for (final CPrimitives primitive : requiredMemoryModelFeatures.getDataOnHeapRequired()) {
			final int bytesize = 0;
			if (getDataHeapArray(primitive) == hda) {
				bytesizes2primitives.addPair(bytesize, primitive);
			}
		}
		final List<ReadWriteDefinition> result = new ArrayList<>();
		for (final Integer bytesize : bytesizes2primitives.getDomain()) {
			final Set<CPrimitives> primitives = bytesizes2primitives.getImage(bytesize);
			final CPrimitives representative = primitives.iterator().next();
			final String procedureName = getProcedureSuffix(representative);
			final ASTType astType =
					mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(), new CPrimitive(representative));
			final boolean alsoUnchecked = DataStructureUtils
					.haveNonEmptyIntersection(requiredMemoryModelFeatures.getUncheckedWriteRequired(), primitives);
			result.add(new ReadWriteDefinition(procedureName, bytesize, astType, primitives, alsoUnchecked));
		}
		return result;
	}

	@Override
	protected int bytesizeOfStoredPointerComponents() {
		return 0;
	}

}
