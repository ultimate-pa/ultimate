package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
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
	private final Boogie2SMT mBoogie2Smt;
	private final Script mScript;

	private FixpointEngineParameters(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage,
			final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> varProvider,
			final ILoopDetector<ACTION> loopDetector, final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final Boogie2SMT boogie2Smt, final Script script) {
		mTransitionProvider = transitionProvider;
		mStorage = storage;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mDomain = domain;
		mBoogie2Smt = boogie2Smt;
		mScript = script;
	}

	public FixpointEngineParameters() {
		this(null, null, null, null, null, null, null);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addTransitionProvider(
			final ITransitionProvider<ACTION, LOCATION> transitionProvider) {
		assert transitionProvider != null;
		return new FixpointEngineParameters<>(transitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mBoogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addStorage(
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage) {
		assert storage != null;
		return new FixpointEngineParameters<>(mTransitionProvider, storage, mVarProvider, mLoopDetector, mDomain,
				mBoogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addVariableProvider(
			final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> varProvider) {
		assert varProvider != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, varProvider, mLoopDetector, mDomain,
				mBoogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addLoopDetector(
			final ILoopDetector<ACTION> loopDetector) {
		assert loopDetector != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, loopDetector, mDomain,
				mBoogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addDomain(
			final IAbstractDomain<STATE, ACTION, VARDECL> domain) {
		assert domain != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, domain,
				mBoogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addBoogie2Smt(final Boogie2SMT boogie2Smt) {
		assert boogie2Smt != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				boogie2Smt, mScript);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> addScript(final Script script) {
		assert script != null;
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mBoogie2Smt, script);
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

	public Script getScript() {
		return mScript;
	}

	public Boogie2SMT getBoogie2Smt() {
		return mBoogie2Smt;
	}

}
