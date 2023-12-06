/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MemorySliceUtils {

	public static final String MEMORY_POINTER = "#memory_$Pointer$";
	public static final String MEMORY_INT = "#memory_int";
	public static final String MEMORY_REAL = "#memory_real";

	public static final String INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_POINTER = "~initToZeroAtPointerBaseAddress~$Pointer$";
	public static final String INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_INT = "~initToZeroAtPointerBaseAddress~int";

	public static final String WRITE_POINTER = "write~$Pointer$";
	public static final String WRITE_UNCHECKED_POINTER = "write~unchecked~$Pointer$";
	public static final String WRITE_INIT_POINTER = "write~init~$Pointer$";
	public static final String READ_POINTER = "read~$Pointer$";
	public static final String READ_UNCHECKED_POINTER = "read~unchecked~$Pointer$";

	public static final String WRITE_INT = "write~int";
	public static final String WRITE_UNCHECKED_INT = "write~unchecked~int";
	public static final String WRITE_INIT_INT = "write~init~int";
	public static final String READ_INT = "read~int";
	public static final String READ_UNCHECKED_INT = "read~unchecked~int";

	public static final String WRITE_REAL = "write~real";
	public static final String WRITE_UNCHECKED_REAL = "write~unchecked~real";
	public static final String WRITE_INIT_REAL = "write~init~real";
	public static final String READ_REAL = "read~real";
	public static final String READ_UNCHECKED_REAL = "read~unchecked~real";

	public static final String ALLOC_ON_STACK = "#Ultimate.allocOnStack";
	public static final String ALLOC_ON_HEAP = "#Ultimate.allocOnHeap";
	public static final String ALLOC_INIT = "#Ultimate.allocInit";
	public static final String ULTIMATE_DEALLOC = "ULTIMATE.dealloc";

	public static final String PTHREADS_FORK_COUNT = "#PthreadsForkCount";
	public static final String PTHREADS_MUTEX = "#PthreadsMutex";
	public static final String PTHREADS_MUTEX_LOCK = "#PthreadsMutexLock";
	public static final String PTHREADS_MUTEX_UNLOCK = "#PthreadsMutexUnlock";
	public static final String PTHREADS_MUTEX_TRYLOCK = "#PthreadsMutexTryLock";
	public static final String PTHREADS_RWLOCK = "#PthreadsRwLock";
	public static final String PTHREADS_RWLOCK_READLOCK = "#PthreadsRwLockReadLock";
	public static final String PTHREADS_RWLOCK_WRITELOCK = "#PthreadsRwLockWriteLock";
	public static final String PTHREADS_RWLOCK_UNLOCK = "#PthreadsRwLockUnlock";

	public static final String ULTIMATE_C_MEMCPY = "#Ultimate.C_memcpy";
	public static final String ULTIMATE_C_MEMMOVE = "#Ultimate.C_memmove";
	public static final String ULTIMATE_C_MEMSET = "#Ultimate.C_memset";
	public static final String ULTIMATE_C_STRCPY = "#Ultimate.C_strcpy";
	public static final String ULTIMATE_C_REALLOC = "#Ultimate.C_realloc";

	private MemorySliceUtils() {
		// do not instantiate
	}

	/**
	 * Replace {@link VariableLHS} if it has one of the given IDs.
	 *
	 * @param suffix
	 * @param oldProcId
	 */
	public static VariableLHS replaceLeftHandSide(final LeftHandSide lhs, final Map<String, String> oldIdToNewId,
			final String oldProcId, final String suffix) {
		if (lhs instanceof VariableLHS) {
			final VariableLHS vlhs = (VariableLHS) lhs;
			final String newId = oldIdToNewId.get(vlhs.getIdentifier());
			final DeclarationInformation newDeclInfo = updateDeclarationInformation(vlhs.getDeclarationInformation(),
					oldProcId, suffix);
			if (newId != null) {
				final VariableLHS result = new VariableLHS(lhs.getLoc(), lhs.getType(), newId, newDeclInfo);
				ModelUtils.copyAnnotations(lhs, result);
				return result;
			} else if (newDeclInfo != vlhs.getDeclarationInformation()) {
				// no ID update but update DeclarationInformation
				final VariableLHS result = new VariableLHS(lhs.getLoc(), lhs.getType(), vlhs.getIdentifier(),
						newDeclInfo);
				ModelUtils.copyAnnotations(lhs, result);
				return result;
			}
		}
		return null;
	}

	/**
	 * Replace {@link IdentifierExpression} if it has one of the given IDs.
	 */
	public static IdentifierExpression replaceIdentifierExpression(final Expression expr,
			final Map<String, String> oldIdToNewId, final String oldProcId, final String suffix) {
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expr;
			final String newId = oldIdToNewId.get(ie.getIdentifier());
			final DeclarationInformation newDeclInfo = updateDeclarationInformation(ie.getDeclarationInformation(),
					oldProcId, suffix);
			if (newId != null) {
				final IdentifierExpression result = new IdentifierExpression(ie.getLoc(), ie.getType(), newId,
						newDeclInfo);
				ModelUtils.copyAnnotations(expr, result);
				return result;
			} else if (newDeclInfo != ie.getDeclarationInformation()) {
				// no ID update but update DeclarationInformation
				final IdentifierExpression result = new IdentifierExpression(ie.getLoc(), ie.getType(),
						ie.getIdentifier(), newDeclInfo);
				ModelUtils.copyAnnotations(expr, result);
				return result;
			}
		}
		return null;
	}

	private static DeclarationInformation updateDeclarationInformation(final DeclarationInformation declInfo,
			final String oldProcId, final String suffix) {
		if (oldProcId == null && suffix == null) {
			return declInfo;
		}
		if (declInfo.getProcedure() == null) {
			// does not have procedure
			return declInfo;
		}
		final String newProcId = oldProcId + suffix;
		if (!declInfo.getProcedure().equals(oldProcId)) {
			throw new AssertionError(String.format("No match! Existing procId %s, oldProcId %s, newProcId %s",
					declInfo.getProcedure(), oldProcId, newProcId));
		}
		return new DeclarationInformation(declInfo.getStorageClass(), newProcId);
	}

	public static String constructMemorySliceSuffix(final int i) {
		return "#" + i;
	}

	public static boolean isPointerArray(final LeftHandSide array) {
		if (array instanceof VariableLHS) {
			final VariableLHS va = (VariableLHS) array;
			if (va.getIdentifier().equals(MemorySliceUtils.MEMORY_POINTER)) {
				return true;
			}
		}
		return false;
	}

	public static boolean isIntArray(final LeftHandSide array) {
		if (array instanceof VariableLHS) {
			final VariableLHS va = (VariableLHS) array;
			if (va.getIdentifier().equals(MemorySliceUtils.MEMORY_INT)) {
				return true;
			}
		}
		return false;
	}

	public static boolean isRealArray(final LeftHandSide array) {
		if (array instanceof VariableLHS) {
			final VariableLHS va = (VariableLHS) array;
			if (va.getIdentifier().equals(MemorySliceUtils.MEMORY_REAL)) {
				return true;
			}
		}
		return false;
	}

	public static boolean containsMemoryArrays(final BoogieASTNode node) {
		final String string = node.toString();
		return (string.contains(MEMORY_POINTER) || string.contains(MEMORY_INT) || string.contains(MEMORY_REAL));
	}

}