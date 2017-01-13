package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngineParameters<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL, LOCATION, EXPRESSION> {
	
	private final ITransitionProvider<ACTION, LOCATION> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mStorage;
	private final IVariableProvider<STATE, ACTION, VARDECL> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> mDebugHelper;
	private final IProgressAwareTimer mTimer;
	private final int mMaxUnwindings;
	private final int mMaxParallelStates;
	private final ILogger mLogger;
	private final Class<VARDECL> mVariablesType;

	/**
	 * Create {@link FixpointEngineParameters} with default logger, timer and settings from abstract interpretation
	 * settings.
	 */
	private FixpointEngineParameters(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage,
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final ILoopDetector<ACTION> loopDetector,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> debugHelper, final IUltimateServiceProvider services,
			final Class<VARDECL> variablesType) {
		if (services == null) {
			throw new IllegalArgumentException("services may not be null");
		}
		mTransitionProvider = transitionProvider;
		mStorage = storage;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mDomain = domain;
		mDebugHelper = debugHelper;
		mTimer = services.getProgressMonitorService();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IPreferenceProvider ups = services.getPreferenceProvider(Activator.PLUGIN_ID);
		mMaxUnwindings = ups.getInt(AbsIntPrefInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mMaxParallelStates = ups.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
		mVariablesType = variablesType;
	}

	/**
	 * Create {@link FixpointEngineParameters} by specifying all fields.
	 */
	private FixpointEngineParameters(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage,
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final ILoopDetector<ACTION> loopDetector,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> debugHelper, final IProgressAwareTimer timer,
			final ILogger logger, final int maxUnwindings, final int maxParallelStates,
			final Class<VARDECL> variablesType) {
		mTransitionProvider = transitionProvider;
		mStorage = storage;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mDomain = domain;
		mDebugHelper = debugHelper;
		mTimer = timer;
		mLogger = logger;
		mMaxUnwindings = maxUnwindings;
		mMaxParallelStates = maxParallelStates;
		mVariablesType = variablesType;
	}

	/**
	 * Create an initial {@link FixpointEngineParameters} object that can be filled with necessary parameters over time.
	 *
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance to initialize timer, logger, and default settings.
	 */
	public FixpointEngineParameters(final IUltimateServiceProvider services, final Class<VARDECL> variablesType) {
		this(null, null, null, null, null, null, services, variablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setTransitionProvider(final ITransitionProvider<ACTION, LOCATION> transitionProvider) {
		if (transitionProvider == null) {
			throw new IllegalArgumentException("transitionProvider may not be null");
		}
		return new FixpointEngineParameters<>(transitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setStorage(final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage) {
		if (storage == null) {
			throw new IllegalArgumentException("storage may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, storage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setVariableProvider(final IVariableProvider<STATE, ACTION, VARDECL> varProvider) {
		if (varProvider == null) {
			throw new IllegalArgumentException("varProvider may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, varProvider, mLoopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setLoopDetector(final ILoopDetector<ACTION> loopDetector) {
		if (loopDetector == null) {
			throw new IllegalArgumentException("loopDetector may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, loopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setDomain(final IAbstractDomain<STATE, ACTION, VARDECL> domain) {
		if (domain == null) {
			throw new IllegalArgumentException("domain may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, domain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setDebugHelper(final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> debugHelper) {
		if (debugHelper == null) {
			throw new IllegalArgumentException("debugHelper may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				debugHelper, mTimer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setTimer(final IProgressAwareTimer timer) {
		if (timer == null) {
			throw new IllegalArgumentException("timer may not be null");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper, timer, mLogger, mMaxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setMaxUnwindings(final int maxUnwindings) {
		if (maxUnwindings <= 0) {
			throw new IllegalArgumentException("maxUnwindings must be larger than zero");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, maxUnwindings, mMaxParallelStates, mVariablesType);
	}

	public FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION, EXPRESSION>
			setMaxParallelStates(final int maxParallelStates) {
		if (maxParallelStates <= 0) {
			throw new IllegalArgumentException("maxParallelStates must be larger than zero");
		}
		return new FixpointEngineParameters<>(mTransitionProvider, mStorage, mVarProvider, mLoopDetector, mDomain,
				mDebugHelper, mTimer, mLogger, mMaxUnwindings, maxParallelStates, mVariablesType);
	}

	public boolean isValid() {
		return getTransitionProvider() != null && getStorage() != null && getVariableProvider() != null
				&& getLoopDetector() != null && getAbstractDomain() != null && getDebugHelper() != null
				&& getTimer() != null && getLogger() != null && getMaxUnwindings() > 0 && getMaxParallelStates() > 0;
	}

	public ITransitionProvider<ACTION, LOCATION> getTransitionProvider() {
		return mTransitionProvider;
	}

	public IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> getStorage() {
		return mStorage;
	}

	public IVariableProvider<STATE, ACTION, VARDECL> getVariableProvider() {
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

	public IProgressAwareTimer getTimer() {
		return mTimer;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public int getMaxUnwindings() {
		return mMaxUnwindings;
	}

	public int getMaxParallelStates() {
		return mMaxParallelStates;
	}

	public Class<VARDECL> getVariablesType() {
		return mVariablesType;
	}
}
