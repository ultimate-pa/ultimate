package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

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
	ThreadPoolExecutor mExecutor;
	Set<L> mPathProgramRepresentative; // Needs to be a Set of words
	int mRunningThreadForPP = 0;
	protected final ILogger mLogger;
	boolean mLoopAccelerationWasTried = false;
	int mImperfectSequencesSoFar = 0;

	/*
	 * call getStrategyForWorker() to get the strategy that we want to execute. This class maintains the overview of our
	 * parallel strategy. We can give any array of tracechecks and make it a parallel strategy
	 */
	public ParallelRefinementStrategy(final ILogger logger, final Set<L> pathProgramRepresentative,
			final int threadLimit) {
		mLogger = logger;
		mPathProgramRepresentative = pathProgramRepresentative;
		mExecutor = createExecutorForPathProgram(mPathProgramRepresentative.hashCode(), threadLimit);
	}

	/*
	 * Future Work, enable different priorities for different strategy modules
	 */
	public void setPriorities(final Integer[] priorities) {

	}

	public void reportImperfectSequence() {
		mImperfectSequencesSoFar += 1;
	}

	/*
	 * default always generalize since we dont have the union yet
	 */
	public boolean generalize() {
		final boolean condition = mImperfectSequencesSoFar >= 1;
		mImperfectSequencesSoFar = 0;
		return condition;
	}

	/*
	 * returns one module for one worker TODO: For SV-Comp settings / evlautions 1 size thread pool, queue (craig,
	 * forward backward) then(craig, acceleration)
	 *
	 * Craig is basically our quick check?
	 *
	 * Still we want to kill all threads if one sequence is perfect
	 */
	public IIpTcStrategyModule<?, L>[] getModule(final StrategyFactory<L>.StrategyModuleFactory factory, int module) {
		final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();
		module = module % 4;
		switch (module) {
		case 0:
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation));
			break;
		case 1:
			rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			break;
		case 2:
			// rtr.add(factory.createIpTcStrategyModuleMathsat(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation));
			// rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_NestedInterpolation));
			break;
		case 3:
			if (!mLoopAccelerationWasTried) {
				rtr.add(factory.createIpTcStrategyModuleAcceleratedTraceCheck());
				mLoopAccelerationWasTried = true;
			} else {
				rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			}
			// rtr.add(factory.createIpTcStrategyModuleCVC4(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			// rtr.add(factory.createIpTcStrategyModuleAbstractInterpretation());
			// rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.BackwardPredicates));
			break;
		default:
			throw new AssertionError("Unknown Module");
		}
		assert rtr.size() == 1;
		mRunningThreadForPP += 1;
		return rtr.toArray(new IIpTcStrategyModule[1]);
	}

	private ThreadPoolExecutor createExecutorForPathProgram(final int traceHash, final int threadLimit) {
		final ThreadFactory factory = new GroupedThreadFactory("PP-" + traceHash + "-");
		// Executor Services for different thread groups
		final long keepAliveTime = 15L; // We want to keep them alive for ever
		final TimeUnit timeUnit = TimeUnit.MINUTES;
		final ThreadPoolExecutor executor =
				new ThreadPoolExecutor(1, threadLimit, keepAliveTime, timeUnit, new LinkedBlockingQueue<>());
		return executor;

	}

	public ExecutorService getExecutor() {
		return mExecutor;
	}

	public int getRunningThreadsOfPP() {
		return mRunningThreadForPP;
	}

	// not used atm
	public boolean isActiveModule(final int module) {
		return true;
	}

	public void updateExecutorSizes(final int newSize) {
		mExecutor.setCorePoolSize(newSize);
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
