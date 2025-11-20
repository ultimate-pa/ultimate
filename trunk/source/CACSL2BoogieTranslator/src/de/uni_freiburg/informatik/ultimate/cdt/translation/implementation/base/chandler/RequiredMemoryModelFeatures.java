package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 *
 * Note that this class has two freezing mechanisms. (Here, freezing means that at some point we set a flag and after
 * that nothing may change anymore in the class members associated with the flag.)
 * <li>One for the query if any Memory Structure features are required (PostProcessor queries this because it needs to
 * know for the init procedure.).
 * <li>At the start of {@link MemoryHandler#declareMemoryStructureInfrastructure(CHandler, ILocation, IASTNode)}, the
 * method {@link RequiredMemoryModelFeatures#finish()} is called. This method resolves dependencies between the
 * different Memory Structure features (e.g. memcpy requires write_unchecked procedures for all heap data arrays),
 * afterwards it freezes those features.
 *
 * Background: There are different dependencies between features recorded in this class. Simple ones are resolved
 * immediately (e.g. reportPointerUncheckedWriteRequired, triggers reportPointerOnHeapRequired). Others are resolved
 * during finish().
 */
public final class RequiredMemoryModelFeatures {

	/**
	 * This flag must be set if any of the Memory Structure features are required.
	 */
	private boolean mMemoryStructureInfrastructureRequired;

	private final Set<CPrimitives> mDataOnHeapRequired;
	private final Set<CPrimitives> mDataUncheckedWriteRequired;
	private final Set<CPrimitives> mDataInitWriteRequired;
	private boolean mPointerOnHeapRequired;
	private boolean mPointerUncheckedWriteRequired;
	private boolean mPointerInitWriteRequired;
	private final Set<MemoryModelDeclarations> mRequiredMemoryStructureDeclarations;

	/**
	 * Set of HeapDataArrays for which constant array initialization is required. (for those we create a Boogie function
	 * with smtdefined attribute..)
	 */
	private final Set<CPrimitives> mDataOnHeapInitFunctionRequired;
	private boolean mPointerOnHeapInitFunctionRequired;

	private final Set<CPrimitives> mDataOnHeapStoreFunctionRequired;
	private boolean mPointerOnHeapStoreFunctionRequired;

	/**
	 * Once this flag is set, no member of this class may be changed anymore.
	 */
	private boolean mIsFrozen;

	private boolean mMemoryStructureInfrastructureRequiredHasBeenQueried;

	private final List<MemoryModelDeclarations> mMetaDataDeclarations;

	public RequiredMemoryModelFeatures(final List<MemoryModelDeclarations> metaDataDeclarations) {
		mDataOnHeapRequired = new HashSet<>();
		mRequiredMemoryStructureDeclarations = new HashSet<>();
		mDataUncheckedWriteRequired = new HashSet<>();
		mDataInitWriteRequired = new HashSet<>();
		mDataOnHeapInitFunctionRequired = new HashSet<>();
		mDataOnHeapStoreFunctionRequired = new HashSet<>();

		mMetaDataDeclarations = metaDataDeclarations;
	}

	public boolean requireMemoryStructureInfrastructure() {
		if (mMemoryStructureInfrastructureRequired) {
			return false;
		}
		if (mMemoryStructureInfrastructureRequiredHasBeenQueried) {
			final String msg =
					"someone already asked if Memory Structure infrastructure was required and we " + "said no";
			assert false : msg;
		}
		mMemoryStructureInfrastructureRequired = true;

		for (final var metaDataDeclaration : mMetaDataDeclarations) {
			require(metaDataDeclaration);
		}

		return true;
	}

	public boolean reportPointerOnHeapRequired() {
		if (mPointerOnHeapRequired) {
			return false;
		}
		checkNotFrozen();
		requireMemoryStructureInfrastructure();
		mPointerOnHeapRequired = true;
		return true;
	}

	public boolean reportPointerUncheckedWriteRequired() {
		if (mPointerUncheckedWriteRequired) {
			return false;
		}
		checkNotFrozen();
		reportPointerOnHeapRequired();
		mPointerUncheckedWriteRequired = true;
		return true;
	}

	public boolean reportPointerInitWriteRequired() {
		if (mPointerInitWriteRequired) {
			return false;
		}
		checkNotFrozen();
		reportPointerOnHeapRequired();
		mPointerInitWriteRequired = true;
		return true;
	}

	public boolean reportDataOnHeapRequired(final CPrimitives primitive) {
		if (mDataOnHeapRequired.contains(primitive)) {
			return false;
		}
		checkNotFrozen();
		requireMemoryStructureInfrastructure();
		mDataOnHeapRequired.add(primitive);
		return true;
	}

	public boolean reportUncheckedWriteRequired(final CPrimitives primitive) {
		if (mDataUncheckedWriteRequired.contains(primitive)) {
			return false;
		}
		checkNotFrozen();
		reportDataOnHeapRequired(primitive);
		mDataUncheckedWriteRequired.add(primitive);
		return true;
	}

	public boolean reportInitWriteRequired(final CPrimitives prim) {
		if (mDataInitWriteRequired.contains(prim)) {
			return false;
		}
		checkNotFrozen();
		reportDataOnHeapRequired(prim);
		mDataInitWriteRequired.add(prim);
		return true;
	}

	public boolean reportDataOnHeapInitFunctionRequired(final CPrimitives prim) {
		if (mDataOnHeapInitFunctionRequired.contains(prim)) {
			return false;
		}
		checkNotFrozen();
		reportDataOnHeapRequired(prim);
		mDataOnHeapInitFunctionRequired.add(prim);
		return true;
	}

	public boolean reportPointerOnHeapInitFunctionRequired() {
		if (mPointerOnHeapInitFunctionRequired) {
			return false;
		}
		checkNotFrozen();
		reportPointerOnHeapRequired();
		mPointerOnHeapInitFunctionRequired = true;
		return true;
	}

	public boolean reportDataOnHeapStoreFunctionRequired(final CPrimitives prim) {
		if (mDataOnHeapStoreFunctionRequired.contains(prim)) {
			return false;
		}
		checkNotFrozen();
		reportDataOnHeapRequired(prim);
		mDataOnHeapStoreFunctionRequired.add(prim);
		return true;
	}

	public boolean reportPointerOnHeapStoreFunctionRequired() {
		if (mPointerOnHeapStoreFunctionRequired) {
			return false;
		}
		checkNotFrozen();
		reportPointerOnHeapRequired();
		mPointerOnHeapStoreFunctionRequired = true;
		return true;
	}

	public boolean isPointerOnHeapRequired() {
		checkIsFrozen();
		return mPointerOnHeapRequired;
	}

	public boolean isPointerUncheckedWriteRequired() {
		checkIsFrozen();
		return mPointerUncheckedWriteRequired;
	}

	public boolean isPointerInitRequired() {
		checkIsFrozen();
		return mPointerInitWriteRequired;
	}

	public Set<CPrimitives> getDataOnHeapRequired() {
		checkIsFrozen();
		return mDataOnHeapRequired;
	}

	public boolean isPointerOnHeapInitFunctionRequired() {
		checkIsFrozen();
		return mPointerOnHeapInitFunctionRequired;
	}

	public boolean isDataOnHeapInitFunctionRequired(final CPrimitives prim) {
		checkIsFrozen();
		return mDataOnHeapInitFunctionRequired.contains(prim);
	}

	public boolean isPointerOnHeapStoreFunctionRequired() {
		checkIsFrozen();
		return mPointerOnHeapStoreFunctionRequired;
	}

	public boolean isDataOnHeapStoreFunctionRequired(final CPrimitives prim) {
		checkIsFrozen();
		return mDataOnHeapStoreFunctionRequired.contains(prim);
	}

	public Set<CPrimitives> getUncheckedWriteRequired() {
		checkIsFrozen();
		return mDataUncheckedWriteRequired;
	}

	public Set<CPrimitives> getInitWriteRequired() {
		checkIsFrozen();
		return mDataInitWriteRequired;
	}

	public boolean isMemoryStructureInfrastructureRequired() {
		mMemoryStructureInfrastructureRequiredHasBeenQueried = true;
		return mMemoryStructureInfrastructureRequired;
	}

	/**
	 *
	 * @param mmdecl
	 * @return true if a change was made
	 */
	public boolean require(final MemoryModelDeclarations mmdecl) {
		if (mRequiredMemoryStructureDeclarations.contains(mmdecl)) {
			// mmdecl has already been added -- nothing to do
			return false;
		}
		checkNotFrozen();
		requireMemoryStructureInfrastructure();
		return mRequiredMemoryStructureDeclarations.add(mmdecl);
	}

	public Set<MemoryModelDeclarations> getRequiredMemoryStructureDeclarations() {
		checkIsFrozen();
		return Collections.unmodifiableSet(mRequiredMemoryStructureDeclarations);
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
			for (final MemoryModelDeclarations mmdecl : new HashSet<>(mRequiredMemoryStructureDeclarations)) {
				changedSomething |= mmdecl.resolveDependencies(this, settings);
			}
		}
		mIsFrozen = true;
	}

	private void checkIsFrozen() {
		if (!mIsFrozen) {
			throw new AssertionError("attempt to query before this has been frozen -- results might be wrong");
		}
	}

	private void checkNotFrozen() {
		if (mIsFrozen) {
			throw new AssertionError("attempt to modify, although this has been frozen already, "
					+ "note that if some Memory Structure feature relies on another one, this has to be declared in"
					+ "MemoryStructureDeclarations.resolveDependencies(..)"
					+ "perhaps we need to update a method there");
		}
	}

	Set<CPrimitives> getDataOnHeapRequiredUnchecked() {
		return mDataOnHeapRequired;
	}

	boolean isPointerOnHeapRequiredUnchecked() {
		return mPointerOnHeapRequired;
	}
}
