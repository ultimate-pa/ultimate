package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.ConditionalCommutativityCriterionChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCriterion;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceConditionGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class CommutativityConditionChecker<L extends IIcfgTransition<?>> implements IConditionalCommutativityChecker<L>{
	
	
	ConditionalCommutativityCriterionChecker<L> mCriterionChecker;
	private IUltimateServiceProvider mServices;
	private IAutomaton<L, IPredicate> mAbstraction;
	private TaskIdentifier mTaskIdentifier;
	private IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private StrategyFactory<L> mStrategyFactory;
	public CommutativityConditionChecker(IConditionalCommutativityCriterion<L> criterion, IIndependenceRelation<IPredicate, L> independenceRelation,
			SemanticIndependenceConditionGenerator generator, final IUltimateServiceProvider services, final IAutomaton<L, IPredicate> abstraction, 
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final StrategyFactory<L> strategyFactory){
		
		mCriterionChecker = new ConditionalCommutativityCriterionChecker<L>(criterion, independenceRelation, generator);
		mServices = services;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mEmptyStackFactory = emptyStackFactory;
		mStrategyFactory = strategyFactory;
	}

	@Override
	public boolean checkConditionalCommutativity(IRun<L, IPredicate> run, IPredicate state, L a, L b) {

		IPredicate condition = mCriterionChecker.getCondition(run, state, a, b);
		if (condition != null && mCriterionChecker.checkCondition()) {
			ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(mServices, run, mAbstraction, mTaskIdentifier, mEmptyStackFactory,
					IPreconditionProvider.constructDefaultPreconditionProvider(), new CommutativityConditionProvider(condition));
			if(strategy.nextFeasibilityCheck().isCorrect().equals(LBool.UNSAT)) {
				return true;
			}
		}		
		return false;
	}
	
	private class CommutativityConditionProvider implements IPostconditionProvider{
		
		IPredicate mCondition;
		public CommutativityConditionProvider(IPredicate condition) {
			mCondition = condition;
		}

		@Override
		public IPredicate constructPostcondition(IPredicateUnifier predicateUnifier) {
			return predicateUnifier.getOrConstructPredicate(mCondition);
		}
	}
}
