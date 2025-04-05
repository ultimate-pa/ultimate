package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadFactory;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

public class ParallelRefinementStrategy<L extends IIcfgTransition<?>> {

	ArrayList<IIpTcStrategyModule> mModules = new ArrayList<>();
	boolean[] mActiveModules; // if mActiveModules[3] = true than a thread uses mModules[3]
	Integer[] mPriorities;
	ThreadGroup mThreadGroup;
	ExecutorService mExecutor;
	Set<L> mPathProgramRepresentative; // Needs to be a Set of words
	int mRunningThreadForPP = 0;
	int mThreadLimitForPP;
	protected final ILogger mLogger;
	boolean mLoopAccelerationWasTried = false;
	int mImperfectSequencesSoFar = 0;

	/*
	 * call getStrategyForWorker() to get the strategy that we want to execute. This class maintains the overview of our
	 * parallel strategy. We can give any array of tracechecks and make it a parallel strategy
	 */
	public ParallelRefinementStrategy(final ILogger logger, final Set<L> pathProgramRepresentative,
			final int threadLimitForThisPP) {

		mThreadLimitForPP = threadLimitForThisPP;
		mLogger = logger;
		mPathProgramRepresentative = pathProgramRepresentative;
		mExecutor = createExecutorForPathProgram(mPathProgramRepresentative.hashCode(), mThreadLimitForPP);
		mActiveModules = new boolean[mThreadLimitForPP];
		// Default priority is from current thread
		mPriorities =
				Collections.nCopies(mThreadLimitForPP, Thread.currentThread().getPriority()).toArray(new Integer[0]);

	}

	/*
	 * Not used yet, maybe we want to submit to executor in this class such that we can set the prio here
	 */
	public void setPriorities(final Integer[] priorities) {
		assert priorities.length == mThreadLimitForPP;
		mPriorities = priorities;
	}

	public void reportImperfectSequence() {
		mImperfectSequencesSoFar += 1;
	}

	public boolean generalize() {
		final boolean condition = mImperfectSequencesSoFar > 1;
		mImperfectSequencesSoFar = 0;
		return condition;
	}
	// public int getPriorityForCurrentModule(final IIpTcStrategyModule<?, L> module) {
	// assert mModules != null;
	// for (int i = 0; i < mModules.length; i++) {
	// if (mModules[i].equals(module)) {
	// return mPriorities[i];
	// }
	// }
	// throw new AssertionError("Unknown Module, no Priority");
	// }

	/*
	 * returns the single module and strategy that is next in line for the next free worker TODO we can also support a
	 * subset of modules here
	 */
	//
	// public IIpTcStrategyModule<?, L>[] getStrategyForWorker(final ITraceCheckStrategyModule<L, ?>[]
	// traceCheckModules) {
	// mModules = (IIpTcStrategyModule<?, L>[]) traceCheckModules;
	// mThreadLimitForPP = traceCheckModules.length;
	// assert mRunningThreadForPP < mThreadLimitForPP;
	// assert mActiveModules.length >= traceCheckModules.length;
	// // richtiges gezwonkel!
	// for (int i = 0; i < mThreadLimitForPP; i++) {
	// if (!mActiveModules[i]) {
	// final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();
	// rtr.add((IIpTcStrategyModule<?, L>) traceCheckModules[i]);
	// final IIpTcStrategyModule<?, L>[] singelModule = rtr.toArray(new IIpTcStrategyModule[rtr.size()]);
	// mRunningThreadForPP += 1;
	// mLogger.info("Running Strategy: " + ((ThreadGroup) singelModule[0]).getName());
	// mActiveModules[i] = true;
	// return singelModule;
	// }
	// }
	// throw new AssertionError(
	// "Caller needs to ensure there are enough modules and not all are running, Is done in startWorker()");
	// }

	/*
	 * returns one module for one worker
	 */
	public IIpTcStrategyModule<?, L>[] getModule(final StrategyFactory<L>.StrategyModuleFactory factory,
			final int module) {
		final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();

		// Idee currentModule just counts up, and we do modulo and we take the new assertion order
		// example 1 then non-inc, 5 then module 1 with new assertio order
		// TODO track active
		// if (!mActiveModules[module]) {
		// mActiveModules[module] = true;
		// }

		switch (module) {
		case 0:
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation));
			break;
		case 1:
			rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.ForwardPredicates));
			break;
		case 2:
			// rtr.add(factory.createIpTcStrategyModuleMathsat(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			if (!mLoopAccelerationWasTried) {
				rtr.add(factory.createIpTcStrategyModuleAcceleratedTraceCheck());
				mLoopAccelerationWasTried = true;
			}
			// rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_NestedInterpolation));
			break;
		case 3:
			// rtr.add(factory.createIpTcStrategyModuleCVC4(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			// rtr.add(factory.createIpTcStrategyModuleAbstractInterpretation());
			rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.BackwardPredicates));
			break;
		default:
			throw new AssertionError("Unknown Module");
		}
		assert rtr.size() == 1;

		return rtr.toArray(new IIpTcStrategyModule[1]);
	}

	// public void freeStrategyFromDoneWorker(final IIpTcStrategyModule<?, L> module) {
	// for (int i = 0; i < mModules.size(); i++) {
	// if (mModules.get(i).equals(module)) {
	// assert mActiveModules[i];
	// mActiveModules[i] = false;
	// mRunningThreadForPP -= 1;
	// }
	// }
	// }

	/*
	 * returns the global executor if we dont care or the executor we have for a pathprogram if we see a new pathprogram
	 * we return a new executor
	 */
	private ExecutorService createExecutorForPathProgram(final int traceHash, final int threadLimitPerPathProgram) {
		final ThreadFactory factory = new GroupedThreadFactory("PP-" + traceHash + "-");
		// Executor Services for different thread groups
		final ExecutorService executor = Executors.newFixedThreadPool(threadLimitPerPathProgram, factory);
		return executor;

	}

	public ExecutorService getExecutor() {
		return mExecutor;
	}

	public boolean isAtThreadLimit() {
		return mRunningThreadForPP >= mThreadLimitForPP;
	}

	public boolean isActiveModule(final int module) {
		if (module == 2) {
			return false;
		}
		return true;
	}

}

class GroupedThreadFactory implements ThreadFactory {
	private final ThreadGroup threadGroup;
	private final String namePrefix;
	private int threadCount = 0;

	public GroupedThreadFactory(final String groupName) {
		threadGroup = new ThreadGroup(groupName);
		namePrefix = groupName + "-thread-";
	}

	@Override
	public Thread newThread(final Runnable r) {
		return new Thread(threadGroup, r, namePrefix + threadCount++);
	}
}
