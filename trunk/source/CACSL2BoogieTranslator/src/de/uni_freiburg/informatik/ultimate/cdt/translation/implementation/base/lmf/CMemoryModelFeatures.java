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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 *
 * Note that this class has two freezing mechanisms. (Here, freezing means that at some point we set a flag and after
 * that nothing may change anymore in the class members associated with the flag.)
 * <li>One for the query if any memory model features are required (PostProcessor queries this because it needs to know
 * for the init procedure.).
 * <li>At the start of {@link MemoryHandler#declareMemoryModelInfrastructure(CHandler, ILocation, IASTNode)}, the method
 * {@link CMemoryModelFeatures#finish()} is called. This method resolves dependencies between the different memory model
 * features (e.g. memcpy requires write_unchecked procedures for all heap data arrays), afterwards it freezes those
 * features.
 *
 * Background: There are different dependencies between features recorded in this class. Simple ones are resolved
 * immediately (e.g. reportPointerUncheckedWriteRequired, triggers reportPointerOnHeapRequired). Others are resolved
 * during finish().
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public final class CMemoryModelFeatures {

	/**
	 * This flag must be set if any of the memory model features are required.
	 */
	private boolean mMemoryModelInfrastructureRequired;

	private final Set<CPrimitives> mDataOnHeapRequired;
	private final Set<CPrimitives> mDataUncheckedWriteRequired;
	private final Set<CPrimitives> mDataInitWriteRequired;
	private boolean mPointerOnHeapRequired;
	private boolean mPointerUncheckedWriteRequired;
	private boolean mPointerInitWriteRequired;

	/**
	 * Set of HeapDataArrays for which constant array initialization is required. (for those we create a Boogie function
	 * with smtdefined attribute..)
	 */
	private final Set<CPrimitives> mDataOnHeapInitFunctionRequired;
	private boolean mPointerOnHeapInitFunctionRequired;

	private final Set<CPrimitives> mDataOnHeapStoreFunctionRequired;
	private boolean mPointerOnHeapStoreFunctionRequired;

	private final Set<CPrimitives> mDataUncheckedReadRequired;
	private boolean mPointerUncheckedReadRequired;

	public CMemoryModelFeatures() {
		mDataOnHeapRequired = new HashSet<>();
		mDataUncheckedWriteRequired = new HashSet<>();
		mDataInitWriteRequired = new HashSet<>();
		mDataUncheckedReadRequired = new HashSet<>();
		mDataOnHeapInitFunctionRequired = new HashSet<>();
		mDataOnHeapStoreFunctionRequired = new HashSet<>();
	}

	public boolean requireMemoryModelInfrastructure() {
		if (mMemoryModelInfrastructureRequired) {
			return false;
		}
		mMemoryModelInfrastructureRequired = true;
		require(MemoryModelDeclarations.ULTIMATE_LENGTH);
		require(MemoryModelDeclarations.ULTIMATE_VALID);
		return true;
	}

	public boolean reportPointerOnHeapRequired() {
		if (mPointerOnHeapRequired) {
			return false;
		}
		requireMemoryModelInfrastructure();
		mPointerOnHeapRequired = true;
		return true;
	}

	public boolean reportPointerUncheckedWriteRequired() {
		if (mPointerUncheckedWriteRequired) {
			return false;
		}
		reportPointerOnHeapRequired();
		mPointerUncheckedWriteRequired = true;
		return true;
	}

	public boolean reportPointerUncheckedReadRequired() {
		if (mPointerUncheckedReadRequired) {
			return false;
		}
		reportPointerOnHeapRequired();
		mPointerUncheckedReadRequired = true;
		return true;
	}

	public boolean reportPointerInitWriteRequired() {
		if (mPointerInitWriteRequired) {
			return false;
		}
		reportPointerOnHeapRequired();
		mPointerInitWriteRequired = true;
		return true;
	}

	public boolean reportDataOnHeapRequired(final CPrimitives primitive) {
		if (mDataOnHeapRequired.contains(primitive)) {
			return false;
		}
		requireMemoryModelInfrastructure();
		mDataOnHeapRequired.add(primitive);
		return true;
	}

	public boolean reportUncheckedReadRequired(final CPrimitives primitive) {
		if (mDataUncheckedReadRequired.contains(primitive)) {
			return false;
		}
		reportDataOnHeapRequired(primitive);
		mDataUncheckedReadRequired.add(primitive);
		return true;
	}

	public boolean reportUncheckedWriteRequired(final CPrimitives primitive) {
		if (mDataUncheckedWriteRequired.contains(primitive)) {
			return false;
		}
		reportDataOnHeapRequired(primitive);
		mDataUncheckedWriteRequired.add(primitive);
		return true;
	}

	public boolean reportInitWriteRequired(final CPrimitives prim) {
		if (mDataInitWriteRequired.contains(prim)) {
			return false;
		}
		reportDataOnHeapRequired(prim);
		mDataInitWriteRequired.add(prim);
		return true;
	}

	public boolean reportDataOnHeapInitFunctionRequired(final CPrimitives prim) {
		if (mDataOnHeapInitFunctionRequired.contains(prim)) {
			return false;
		}
		reportDataOnHeapRequired(prim);
		mDataOnHeapInitFunctionRequired.add(prim);
		return true;
	}

	public boolean reportPointerOnHeapInitFunctionRequired() {
		if (mPointerOnHeapInitFunctionRequired) {
			return false;
		}
		reportPointerOnHeapRequired();
		mPointerOnHeapInitFunctionRequired = true;
		return true;
	}

	public boolean reportDataOnHeapStoreFunctionRequired(final CPrimitives prim) {
		if (mDataOnHeapStoreFunctionRequired.contains(prim)) {
			return false;
		}
		reportDataOnHeapRequired(prim);
		mDataOnHeapStoreFunctionRequired.add(prim);
		return true;
	}

	public boolean reportPointerOnHeapStoreFunctionRequired() {
		if (mPointerOnHeapStoreFunctionRequired) {
			return false;
		}
		reportPointerOnHeapRequired();
		mPointerOnHeapStoreFunctionRequired = true;
		return true;
	}

	public boolean isPointerOnHeapRequired() {
		return mPointerOnHeapRequired;
	}

	public boolean isPointerUncheckedWriteRequired() {
		return mPointerUncheckedWriteRequired;
	}

	public boolean isPointerUncheckedReadRequired() {
		return mPointerUncheckedReadRequired;
	}

	public boolean isPointerInitRequired() {
		return mPointerInitWriteRequired;
	}

	public Set<CPrimitives> getDataOnHeapRequired() {
		return mDataOnHeapRequired;
	}

	public boolean isPointerOnHeapInitFunctionRequired() {
		return mPointerOnHeapInitFunctionRequired;
	}

	public boolean isDataOnHeapInitFunctionRequired(final CPrimitives prim) {
		return mDataOnHeapInitFunctionRequired.contains(prim);
	}

	public boolean isPointerOnHeapStoreFunctionRequired() {
		return mPointerOnHeapStoreFunctionRequired;
	}

	public boolean isDataOnHeapStoreFunctionRequired(final CPrimitives prim) {
		return mDataOnHeapStoreFunctionRequired.contains(prim);
	}

	public Set<CPrimitives> getUncheckedReadRequired() {
		return mDataUncheckedReadRequired;
	}

	public Set<CPrimitives> getUncheckedWriteRequired() {
		return mDataUncheckedWriteRequired;
	}

	public Set<CPrimitives> getInitWriteRequired() {
		return mDataInitWriteRequired;
	}

	public boolean isMemoryModelInfrastructureRequired() {
		return mMemoryModelInfrastructureRequired;
	}

	/**
	 *
	 * @param mmdecl
	 * @return true if a change was made
	 */
	public boolean require(final MemoryModelDeclarations mmdecl) {
		if (mRequiredMemoryModelDeclarations.contains(mmdecl)) {
			// mmdecl has already been added -- nothing to do
			return false;
		}
		requireMemoryModelInfrastructure();
		return mRequiredMemoryModelDeclarations.add(mmdecl);
	}

	/**
	 * <ul>
	 * <li>
	 * <li>make all members of this class unmodifiable from this point on
	 * </ul>
	 *
	 * @param settings
	 */
	public void finish(final TranslationSettings settings) {
		boolean changedSomething = true;
		while (changedSomething) {
			changedSomething = false;
			for (final MemoryModelDeclarations mmdecl : new HashSet<>(mRequiredMemoryModelDeclarations)) {
				changedSomething |= mmdecl.resolveDependencies(this, settings);
			}
		}
	}
}