/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

public class MemoryModelDeclarationsHandler {
	private final Map<MemoryModelDeclarations, MemoryModelDeclarationInfo> mDeclarationInfos;

	private final ITypeHandler mTypeHandler;
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final CPrimitive mRWLockCounterType;

	public MemoryModelDeclarationsHandler(final ITypeHandler typeHandler, final IBooleanArrayHelper booleanArrayHelper,
			final CPrimitive rWLockCounterType) {
		mDeclarationInfos = new LinkedHashMap<>();

		mTypeHandler = typeHandler;
		mBooleanArrayHelper = booleanArrayHelper;
		mRWLockCounterType = rWLockCounterType;
	}

	public MemoryModelDeclarationInfo memoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		final var result = mDeclarationInfos.get(mmd);
		if (result == null) {
			throw new AssertionError("Call requireMemoryStructureFeature first for key: " + mmd);
		}

		return result;
	}

	public void createMemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		mDeclarationInfos.putIfAbsent(mmd, constructMemoryStructureDeclarationInfo(mmd));
	}

	private MemoryModelDeclarationInfo constructMemoryStructureDeclarationInfo(final MemoryModelDeclarations mmd) {
		switch (mmd) {
		case ULTIMATE_DATA_RACE_MEMORY:
			return new MemoryModelDeclarationInfo(mmd, BoogieType.createArrayType(0,
					new BoogieType[] { mTypeHandler.getBoogiePointerType() },
					mTypeHandler.getBoogieTypeForBoogieASTType(mBooleanArrayHelper.constructBoolReplacementType())));
		case ULTIMATE_HEAP_ALLOCATIONS:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
		case ULTIMATE_INITIAL_ALLOCATIONS:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
		case ULTIMATE_LENGTH:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
							mTypeHandler.getBoogieTypeForSizeT()));
		case ULTIMATE_PTHREADS_FORK_COUNT:
			return new MemoryModelDeclarationInfo(mmd,
					mTypeHandler.getBoogieTypeForCType(mTypeHandler.getThreadIdType()));
		case ULTIMATE_PTHREADS_MUTEX:
			return new MemoryModelDeclarationInfo(mmd, BoogieType.createArrayType(0,
					new BoogieType[] { mTypeHandler.getBoogiePointerType() },
					mTypeHandler.getBoogieTypeForBoogieASTType(mBooleanArrayHelper.constructBoolReplacementType())));
		case ULTIMATE_PTHREADS_RWLOCK:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() },
							mTypeHandler.getBoogieTypeForCType(mRWLockCounterType)));
		case ULTIMATE_STACK_ALLOCATIONS:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
		case ULTIMATE_STACK_HEAP_BARRIER:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
		case ULTIMATE_VALID:
			return new MemoryModelDeclarationInfo(mmd, BoogieType.createArrayType(0,
					new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
					mTypeHandler.getBoogieTypeForBoogieASTType(mBooleanArrayHelper.constructBoolReplacementType())));
		default:
			return new MemoryModelDeclarationInfo(mmd);
		}
	}
}
