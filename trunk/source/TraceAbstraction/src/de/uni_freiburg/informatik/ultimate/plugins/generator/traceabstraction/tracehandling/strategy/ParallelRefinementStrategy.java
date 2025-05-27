package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

/**
 * This class provides a framework for parallel strategies. There is one instance of this class per path program It
 * provides an executioner for its path program It provides a modules depending how often we have seen this path program
 * and on the mode we ware in (int or bit-precise)
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class ParallelRefinementStrategy<L extends IIcfgTransition<?>> {
	ArrayList<IIpTcStrategyModule> mModules = new ArrayList<>();
	boolean[] mActiveModules;
	Integer[] mPriorities;
	ThreadGroup mThreadGroup;
	ThreadPoolExecutor mExecutor;
	Set<L> mPathProgramRepresentative; // Needs to be a Set of words
	int mRunningThreadForPP = 0;
	protected final ILogger mLogger;
	boolean mLoopAccelerationWasTried = false; // Default is false, we want to accelerate once per PP
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
		// if (mImperfectInterpolantAutomaton == null) {
		// mImperfectInterpolantAutomaton = newImperfectInterpolantAutomaton;
		// } else {
		// mImperfectInterpolantAutomaton =
		// createUnionOfInterpolantAutomata(new AutomataLibraryServices(iUltimateServiceProvider),
		// stateFactory, newImperfectInterpolantAutomaton);
		// }
		mImperfectSequencesSoFar += 1;
	}

	/**
	 * TODO When we have a NWA Union that is capable of unionizing two automata from different scripts, we can collect
	 * interpolant automata from imperfect sequences here. Then generalize their union as soon as we have a certain
	 * amount collected.
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

		final Union<L, IPredicate> union = null; // TODO union for nwa
		// new Union<>(services, stateFactory, newImperfectInterpolantAutomaton, mImperfectInterpolantAutomaton);

		assert union.checkResult(stateFactory);

		return union.getResult();
	}

	/*
	 * TODO in the future we want to generalize only if the sequence was perfect or we have collected a certain amount
	 * of imperfect sequences in a union automaton
	 */
	public WorkerGeneralizationMode generalize() {
		final boolean condition = mImperfectSequencesSoFar >= 1;
		mImperfectSequencesSoFar = 0;
		// TODO so far we have to generalize in worker otherwise we crash
		return WorkerGeneralizationMode.YES;
	}

	/*
	 * Returns modules depending on the amount of times we have seen this path program. TODO: For find best SV-Comp
	 * setting that doesnt need to much CPU time
	 *
	 * We want to do loop acceleration exactly once per PathProgram Trying different Assertion orders is more promising
	 * then trying different solvers
	 */
	public IIpTcStrategyModule<?, L>[] getModule(final StrategyFactory<L>.StrategyModuleFactory factory) {

		final TermClassifier tc = factory.getTermClassifierForTrace();
		final boolean integerMode =
				tc.getOccuringSortNames().contains("Int") || tc.getOccuringSortNames().contains("Real");

		if (integerMode) {
			return getIntegerModule(factory);
		} else {
			return getBitVectorModule(factory, tc);
		}

	}

	private IIpTcStrategyModule<?, L>[] getBitVectorModule(final StrategyFactory<L>.StrategyModuleFactory factory,
			final TermClassifier tc) {
		final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();
		mRunningThreadForPP = mRunningThreadForPP % 6;
		final boolean hasFloats = RefinementStrategyUtils.hasFloats(tc);
		switch (mRunningThreadForPP) {
		case 1:
			if (!mLoopAccelerationWasTried) {
				rtr.add(factory.createIpTcStrategyModuleAcceleratedTraceCheck());
				mLoopAccelerationWasTried = true;
				break;
			}
			//$FALL-THROUGH$
		case 2:
		case 3:
		case 4:
		case 5:
		default:
			if (!hasFloats) {
				rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
				rtr.add(factory.createIpTcStrategyModuleCVC4(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			}
			if (RefinementStrategyUtils.hasNoQuantifiersNoBitvectorExtensions(tc)) {
				// no quantifiers and no FP_TO_IEEE_BV_EXTENSION
				rtr.add(factory.createIpTcStrategyModuleMathsat(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			}
			if (hasFloats) {
				rtr.add(factory.createIpTcStrategyModuleCVC4(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
				rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			}
			break;
		}
		assert rtr.size() >= 1;
		mRunningThreadForPP += 1;
		return rtr.toArray(new IIpTcStrategyModule[1]);
	}

	private IIpTcStrategyModule<?, L>[] getIntegerModule(final StrategyFactory<L>.StrategyModuleFactory factory) {
		final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();
		mRunningThreadForPP = mRunningThreadForPP % 6;
		switch (mRunningThreadForPP) {
		case 1:
			if (!mLoopAccelerationWasTried) {
				rtr.add(factory.createIpTcStrategyModuleAcceleratedTraceCheck());
				mLoopAccelerationWasTried = true;
				break;
			}
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_NestedInterpolation,
					new AssertCodeBlockOrder(AssertCodeBlockOrderType.SMT_FEATURE_HEURISTIC)));
			break;
		case 2:
		case 3:
		case 4:
		case 5:
		default:
			rtr.add(factory.createIpTcStrategyModuleSmtInterpolCraig(InterpolationTechnique.Craig_TreeInterpolation));
			rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
			break;
		}
		assert rtr.size() >= 1;
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

	/*
	 * Every PathProgram has its own executor
	 */
	public ThreadPoolExecutor getExecutor() {
		return mExecutor;
	}

	/*
	 * Tracks how many threads are currently running belonging to this PathProgram Determines the next module
	 */
	public int getRunningThreadsOfPP() {
		return mRunningThreadForPP;
	}

	public void setRunningThreadsOfPP(final int ppSeenThisManyTimesBefore) {
		mRunningThreadForPP = ppSeenThisManyTimesBefore;
	}

	// not used atm
	public boolean isActiveModule(final int module) {
		return true;
	}

	/*
	 * Every PathProgram has its own executor its sice is dynamically changed to threadlimit / #activeExecutors
	 *
	 * Basically the more pathprograms we check in parallel the smaller is the executor size for each This helps us to
	 * distribute the work better between pathprogram, but it is upon our search to actually find multiple pathprograms
	 */
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
