package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngineParameters<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final ITransitionProvider<ACTION, LOCATION> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mStorage;
	private final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> mDebugHelper;

	private FixpointEngineParameters(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage,
			final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> varProvider,
			final ILoopDetector<ACTION> loopDetector, final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> debugHelper) {
		mTransitionProvider = transitionProvider;
		mStorage = storage;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mDomain = domain;
		mDebugHelper = debugHelper;
	}

	public FixpointEngineParameters() {
		this(null, null, null, null, null, null);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addTransitionProvider(
			final ITransitionProvider<ACTION, LOCATION> transitionProvider) {
		assert transitionProvider != null;
		return new FixpointEngineParameters<>(transitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addStorage(
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage) {
		assert storage != null;
		return new FixpointEngineParameters<>(mTransitionProvider, storage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addVariableProvider(
			final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> varProvider) {
		assert varProvider != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, varProvider, mLoopDetector, mDomain,
				mDebugHelper);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addLoopDetector(
			final ILoopDetector<ACTION> loopDetector) {
		assert loopDetector != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, loopDetector, mDomain,
				mDebugHelper);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addDomain(
			final IAbstractDomain<STATE, ACTION, VARDECL> domain) {
		assert domain != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, domain,
				mDebugHelper);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addDebugHelper(
			final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> debugHelper) {
		assert debugHelper != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				debugHelper);
	}

	public ITransitionProvider<ACTION, LOCATION> getTransitionProvider() {
		return mTransitionProvider;
	}

	public IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> getStorage() {
		return mStorage;
	}

	public IVariableProvider<STATE, ACTION, VARDECL, LOCATION> getVariableProvider() {
		return mVarProvider;
	}

	public ILoopDetector<ACTION> getLoopDetector() {
		return mLoopDetector;
	}

	public IAbstractDomain<STATE, ACTION, VARDECL> getAbstractDomain() {
		return mDomain;
	}

	public IDebugHelper<STATE, ACTION, VARDECL, LOCATION> getDebugHelper() {
		return mDebugHelper;
	}
}
