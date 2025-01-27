package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

public enum MemoryModelDeclarations {
	ULTIMATE_ALLOC_STACK("#Ultimate.allocOnStack"),

	/**
	 * This method allow us to allocate memory without costly array updates. The classical memory allocation in the
	 * Hoenicke-Lindenmann memory model returns nodeterministically chosen fresh valid pointers but requires an update
	 * of the #valid array and the #length array. If we have many of these array updates (hundreds, thousands) this
	 * affects the performance of our tool. This method allows us to assume (via ensures clauses) that and how much
	 * memory is valid. This method requires that the fresh pointer is passed as an input. Since we know all memory that
	 * is allocated initially we use a counter in this translation to construct fresh pointers.
	 */
	ULTIMATE_ALLOC_INIT("#Ultimate.allocInit"),

	ULTIMATE_ALLOC_HEAP("#Ultimate.allocOnHeap"),

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

	ULTIMATE_PTHREADS_FORK_COUNT("#PthreadsForkCount"),

	ULTIMATE_PTHREADS_MUTEX("#PthreadsMutex"),

	ULTIMATE_PTHREADS_MUTEX_LOCK("#PthreadsMutexLock"),

	ULTIMATE_PTHREADS_MUTEX_UNLOCK("#PthreadsMutexUnlock"),

	ULTIMATE_PTHREADS_MUTEX_TRYLOCK("#PthreadsMutexTryLock"),

	ULTIMATE_PTHREADS_RWLOCK("#PthreadsRwLock"),

	ULTIMATE_PTHREADS_RWLOCK_READLOCK("#PthreadsRwLockReadLock"),

	ULTIMATE_PTHREADS_RWLOCK_WRITELOCK("#PthreadsRwLockWriteLock"),

	ULTIMATE_PTHREADS_RWLOCK_UNLOCK("#PthreadsRwLockUnlock"),

	ULTIMATE_VALID(SFO.VALID),

	/**
	 * The {@link MemoryModelDeclarations#ULTIMATE_STACK_HEAP_BARRIER} allows us to partition the addresses of our
	 * memory arrays into a stack and a heap. The {@link MemoryModelDeclarations#ULTIMATE_STACK_HEAP_BARRIER} is a
	 * constant whose value is not determined. Each pointer whose address-base is strictly smaller than the barrier
	 * points to the heap, each pointer whose address-base is strictly greater than the barrier points to the stack.
	 */
	ULTIMATE_STACK_HEAP_BARRIER("#StackHeapBarrier"),

	/**
	 * Used to detect data races between concurrent accesses to the same memory location.
	 */
	ULTIMATE_DATA_RACE_MEMORY(SFO.MEMORY_RACE),

	;

	private final String mName;

	MemoryModelDeclarations(final String name) {
		mName = name;
	}

	public String getName() {
		return mName;
	}

	/**
	 *
	 * @param rmmf
	 * @param settings
	 * @return true iff the method execution made a change in rmmf
	 */
	boolean resolveDependencies(final RequiredMemoryModelFeatures rmmf, final TranslationSettings settings) {
		if (this == MemoryModelDeclarations.C_MEMCPY || this == MemoryModelDeclarations.C_MEMMOVE) {
			return memcpyOrMemmoveRequirements(rmmf);
		} else if (this == MemoryModelDeclarations.C_MEMSET) {
			return false;
		} else if (this == MemoryModelDeclarations.ULTIMATE_MEMINIT) {
			return meminitRequirements(rmmf, settings);
		} else if (this == MemoryModelDeclarations.C_STRCPY) {
			return strcpyRequirements(rmmf);
		} else if (this == MemoryModelDeclarations.C_REALLOC) {
			return reallocRequirements(rmmf);
		} else if (this == MemoryModelDeclarations.ULTIMATE_ALLOC_STACK
				|| this == MemoryModelDeclarations.ULTIMATE_ALLOC_HEAP) {
			return allocRequirements(rmmf);
		} else if (this == ULTIMATE_PTHREADS_MUTEX_LOCK || this == ULTIMATE_PTHREADS_MUTEX_UNLOCK
				|| this == ULTIMATE_PTHREADS_MUTEX_TRYLOCK) {
			return rmmf.require(ULTIMATE_PTHREADS_MUTEX);
		} else if (this == ULTIMATE_PTHREADS_RWLOCK_READLOCK || this == ULTIMATE_PTHREADS_RWLOCK_WRITELOCK
				|| this == ULTIMATE_PTHREADS_RWLOCK_UNLOCK) {
			return rmmf.require(ULTIMATE_PTHREADS_RWLOCK);
		} else {
			return false;
		}
	}

	private static boolean allocRequirements(final RequiredMemoryModelFeatures rmmf) {
		boolean changedSomething = false;
		changedSomething |= rmmf.requireMemoryModelInfrastructure();
		changedSomething |= rmmf.require(MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER);
		return changedSomething;
	}

	private static boolean reallocRequirements(final RequiredMemoryModelFeatures rmmf) {
		boolean changedSomething = false;
		changedSomething |= rmmf.requireMemoryModelInfrastructure();
		changedSomething |= rmmf.require(MemoryModelDeclarations.ULTIMATE_DEALLOC);
		for (final CPrimitives prim : rmmf.getDataOnHeapRequiredUnchecked()) {
			changedSomething |= rmmf.reportDataOnHeapStoreFunctionRequired(prim);
		}
		if (rmmf.isPointerOnHeapRequiredUnchecked()) {
			changedSomething |= rmmf.reportPointerOnHeapStoreFunctionRequired();
		}
		return changedSomething;
	}

	private static boolean strcpyRequirements(final RequiredMemoryModelFeatures rmmf) {
		boolean changedSomething = false;
		rmmf.reportDataOnHeapRequired(CPrimitives.CHAR);
		for (final CPrimitives prim : new HashSet<>(rmmf.getDataOnHeapRequiredUnchecked())) {
			changedSomething |= rmmf.reportUncheckedWriteRequired(prim);
		}
		if (rmmf.isPointerOnHeapRequiredUnchecked()) {
			changedSomething |= rmmf.reportPointerUncheckedWriteRequired();
		}
		return changedSomething;
	}

	private static boolean meminitRequirements(final RequiredMemoryModelFeatures rmmf,
			final TranslationSettings settings) {
		boolean changedSomething = false;
		if (settings.useConstantArrays()) {
			// TODO: using members instead of getters here to avoid "checkIsFrozen" calls -- not nice..
			for (final CPrimitives prim : new HashSet<>(rmmf.getDataOnHeapRequiredUnchecked())) {
				changedSomething |= rmmf.reportDataOnHeapInitFunctionRequired(prim);
			}
			if (rmmf.isPointerOnHeapRequiredUnchecked()) {
				changedSomething |= rmmf.reportPointerOnHeapInitFunctionRequired();
			}
		}
		/*
		 * at the moment meminit is using manual assignments, not write calls, that should perhaps be changed --> and
		 * then we need to add the corresponding code here, like e.g. for memmove
		 */
		return changedSomething;
	}

	private static boolean memcpyOrMemmoveRequirements(final RequiredMemoryModelFeatures mmf) {
		boolean changedSomething = false;
		// TODO: using members instead of getters here to avoid "checkIsFrozen" calls -- not nice..
		for (final CPrimitives prim : new HashSet<>(mmf.getDataOnHeapRequiredUnchecked())) {
			changedSomething |= mmf.reportUncheckedWriteRequired(prim);
			changedSomething |= mmf.reportUncheckedReadRequired(prim);
		}
		if (mmf.isPointerOnHeapRequiredUnchecked()) {
			changedSomething |= mmf.reportPointerUncheckedWriteRequired();
			changedSomething |= mmf.reportPointerUncheckedReadRequired();
		}
		changedSomething |= mmf.require(ULTIMATE_DATA_RACE_MEMORY);
		return changedSomething;
	}
}