package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
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
	boolean mLoopAccelerationWasTried = true;
	int mImperfectSequencesSoFar = 0;
	int mExecutorSize = 0;
	INestedWordAutomaton<L, IPredicate> mImperfectInterpolantAutomaton = null;

	public enum WorkerGeneralizationMode {
		YES, NO, ONLYIFPERFECT
	}

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

	public void reportImperfectSequence(final IUltimateServiceProvider iUltimateServiceProvider,
			final PredicateFactoryRefinement stateFactory,
			final INestedWordAutomaton<L, IPredicate> newImperfectInterpolantAutomaton)
			throws AutomataLibraryException {
		if (mImperfectInterpolantAutomaton == null) {
			mImperfectInterpolantAutomaton = newImperfectInterpolantAutomaton;
		} else {
			mImperfectInterpolantAutomaton =
					createUnionOfInterpolantAutomata(new AutomataLibraryServices(iUltimateServiceProvider),
							stateFactory, newImperfectInterpolantAutomaton);
		}
		mImperfectSequencesSoFar += 1;
	}

	/**
	 * TODO debug TODO use
	 *
	 * @param services
	 * @param stateFactory
	 * @param newImperfectInterpolantAutomaton
	 * @return
	 * @throws AutomataLibraryException
	 */
	public INestedWordAutomaton<L, IPredicate> createUnionOfInterpolantAutomata(final AutomataLibraryServices services,
			PredicateFactoryRefinement stateFactory,
			final INestedWordAutomaton<L, IPredicate> newImperfectInterpolantAutomaton)
			throws AutomataLibraryException {
		stateFactory = (PredicateFactoryRefinement) newImperfectInterpolantAutomaton.getStateFactory();
		// assert stateFactory.equals(mImperfectInterpolantAutomaton.getStateFactory());
		// final IntersectDD<L, IPredicate> in = new IntersectDD<>(services, stateFactory,
		// newImperfectInterpolantAutomaton, mImperfectInterpolantAutomaton);
		// in.checkResult(stateFactory);

		final Union<L, IPredicate> union =
				new Union<>(services, stateFactory, newImperfectInterpolantAutomaton, mImperfectInterpolantAutomaton);

		assert union.checkResult(stateFactory);

		return union.getResult();
	}

	/*
	 * default always generalize since we dont have the union yet
	 */
	public WorkerGeneralizationMode generalize() {
		final boolean condition = mImperfectSequencesSoFar >= 1;
		mImperfectSequencesSoFar = 0;
		return WorkerGeneralizationMode.ONLYIFPERFECT;
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
		module = module % 2;
		switch (module) {
		case 0:
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation));
			break;
		case 1:
			if (!mLoopAccelerationWasTried) {
				rtr.add(factory.createIpTcStrategyModuleAcceleratedTraceCheck());
				mLoopAccelerationWasTried = true;
			} else {
				rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			}
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
		mExecutorSize = 1;
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
		mExecutorSize = newSize;
		mExecutor.setCorePoolSize(newSize);
	}

	public int getExecutorSize() {
		return mExecutorSize;
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
