package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class PostConditionTraceChecker<L extends IIcfgTransition<?>> implements ITraceChecker<L>{
	
	

	private IUltimateServiceProvider mServices;
	private IAutomaton<L, IPredicate> mAbstraction;
	private TaskIdentifier mTaskIdentifier;
	private IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private StrategyFactory<L> mStrategyFactory;
	public PostConditionTraceChecker(final IUltimateServiceProvider services, final IAutomaton<L, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, StrategyFactory<L> strategyFactory){

		mServices = services;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mEmptyStackFactory = emptyStackStateFactory;
		mStrategyFactory = strategyFactory;
	}

	public List<IPredicate> checkTrace(IRun<L, IPredicate> run, IPredicate postCondition) {
			ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(mServices, run, mAbstraction, mTaskIdentifier, mEmptyStackFactory,
					IPreconditionProvider.constructDefaultPreconditionProvider(), new PostConditionProvider(postCondition));
			ITraceCheckStrategyModule<L, ?> check = strategy.nextFeasibilityCheck();
			if(check.isCorrect().equals(LBool.UNSAT)) {
				while(strategy.hasNextFeasilibityCheck()){
					if (check instanceof InterpolatingTraceCheck) {
						return ((InterpolatingTraceCheck<?>) check).getIpp().getPredicates();
					}
					check = strategy.nextFeasibilityCheck();
				}
			}	
		return null;
	}
	
	private class PostConditionProvider implements IPostconditionProvider{
		
		IPredicate mCondition;

		public PostConditionProvider(IPredicate condition) {
			mCondition = condition;
		}
	
		@Override
		public IPredicate constructPostcondition(IPredicateUnifier predicateUnifier) {
			return predicateUnifier.getOrConstructPredicate(mCondition);
		}

	}
}
