package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

public enum CModelFeature {
	ULTIMATE_ALLOC(UltimateAlloc.class),

	ULTIMATE_DEALLOC(SFO.DEALLOC),

	/**
	 * (used for calloc)
	 */
	ULTIMATE_MEMINIT(SFO.MEMINIT),

	C_MEMCPY(SFO.C_MEMCPY),

	C_MEMMOVE(SFO.C_MEMMOVE),

	C_MEMSET(SFO.C_MEMSET),

	C_STRCPY(SFO.C_STRCPY),

	C_REALLOC(SFO.C_REALLOC),

	ULTIMATE_LENGTH(SFO.LENGTH),

	ULTIMATE_PTHREADS_MUTEX("#PthreadsMutex"),

	ULTIMATE_PTHREADS_MUTEX_LOCK("#PthreadsMutexLock"),

	ULTIMATE_VALID(SFO.VALID),

	ULTIMATE_STACK_HEAP_BARRIER("#StackHeapBarrier"),

	ULTIMATE_DATA_ON_HEAP_REQUIRED(UltimateDataOnHeapRequired.class),

	;

	private final Class<? extends ICModelFeatureDefinition> mClazz;

	private CModelFeature(final Class<? extends ICModelFeatureDefinition> clazz) {
		mClazz = clazz;
	}

	public Class<? extends ICModelFeatureDefinition> getDefinitionClass() {
		return mClazz;
	}

	/**
	 *
	 * @param rmmf
	 * @param settings
	 * @return true iff the method execution made a change in rmmf
	 */
	boolean resolveDependencies(final CMemoryModelFeatures rmmf, final TranslationSettings settings) {
		if (this == MemoryModelDeclarations.C_MEMCPY || this == MemoryModelDeclarations.C_MEMMOVE) {
			return memcpyOrMemmoveRequirements(rmmf);
		} else if (this == MemoryModelDeclarations.C_MEMSET) {
			return false;
		} else if (this == MemoryModelDeclarations.ULTIMATE_MEMINIT) {
			return meminitRequirements(rmmf, settings);
		} else if (this == MemoryModelDeclarations.C_STRCPY) {
			return strcpyRequirements(rmmf, settings);
		} else if (this == MemoryModelDeclarations.C_REALLOC) {
			return reallocRequirements(rmmf, settings);
		} else {
			return false;
		}
	}

	private boolean reallocRequirements(final CMemoryModelFeatures rmmf, final TranslationSettings settings) {
		boolean changedSomething = false;
		changedSomething |= rmmf.requireMemoryModelInfrastructure();
		changedSomething |= rmmf.require(MemoryModelDeclarations.ULTIMATE_DEALLOC);
		for (final CPrimitives prim : rmmf.mDataOnHeapRequired) {
			changedSomething |= rmmf.reportDataOnHeapStoreFunctionRequired(prim);
		}
		if (rmmf.mPointerOnHeapRequired) {
			changedSomething |= rmmf.reportPointerOnHeapStoreFunctionRequired();
		}
		return changedSomething;
	}

	private boolean strcpyRequirements(final CMemoryModelFeatures rmmf, final TranslationSettings settings) {
		boolean changedSomething = false;
		for (final CPrimitives prim : new HashSet<>(rmmf.mDataOnHeapRequired)) {
			changedSomething |= rmmf.reportUncheckedWriteRequired(prim);
		}
		if (rmmf.mPointerOnHeapRequired) {
			changedSomething |= rmmf.reportPointerUncheckedWriteRequired();
		}
		return changedSomething;
	}

	private boolean meminitRequirements(final CMemoryModelFeatures rmmf, final TranslationSettings settings) {
		boolean changedSomething = false;
		if (settings.useConstantArrays()) {
			// TODO: using members instead of getters here to avoid "checkIsFrozen" calls -- not nice..
			for (final CPrimitives prim : new HashSet<>(rmmf.mDataOnHeapRequired)) {
				changedSomething |= rmmf.reportDataOnHeapInitFunctionRequired(prim);
			}
			if (rmmf.mPointerOnHeapRequired) {
				changedSomething |= rmmf.reportPointerOnHeapInitFunctionRequired();
			}
		}
		/*
		 * at the moment meminit is using manual assignments, not write calls, that should perhaps be changed --> and
		 * then we need to add the corresponding code here, like e.g. for memmove
		 */
		return changedSomething;
	}

	boolean memcpyOrMemmoveRequirements(final CMemoryModelFeatures mmf) {
		boolean changedSomething = false;
		// TODO: using members instead of getters here to avoid "checkIsFrozen" calls -- not nice..
		for (final CPrimitives prim : new HashSet<>(mmf.mDataOnHeapRequired)) {
			changedSomething |= mmf.reportUncheckedWriteRequired(prim);
			changedSomething |= mmf.reportUncheckedReadRequired(prim);
		}
		if (mmf.mPointerOnHeapRequired) {
			changedSomething |= mmf.reportPointerUncheckedWriteRequired();
			changedSomething |= mmf.reportPointerUncheckedReadRequired();
		}
		return changedSomething;
	}
}
