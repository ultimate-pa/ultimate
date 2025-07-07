package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.IBooleanArrayHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

public class MemoryModelDeclarationsHandler {
	private final Map<MemoryModelDeclarations, MemoryModelDeclarationInfo> declarationInfos;

	private final ITypeHandler mTypeHandler;
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final CPrimitive mRWLockCounterType;

	public MemoryModelDeclarationsHandler(final ITypeHandler typeHandler, final IBooleanArrayHelper booleanArrayHelper,
			final CPrimitive rWLockCounterType) {
		declarationInfos = new LinkedHashMap<>();

		mTypeHandler = typeHandler;
		mBooleanArrayHelper = booleanArrayHelper;
		mRWLockCounterType = rWLockCounterType;
	}

	public MemoryModelDeclarationInfo memoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		final var result = declarationInfos.get(mmd);
		if (result == null) {
			throw new AssertionError("Call requireMemoryStructureFeature first for key: " + mmd);
		}

		return result;
	}

	public void createMemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		declarationInfos.putIfAbsent(mmd, constructMemoryStructureDeclarationInfo(mmd));
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
