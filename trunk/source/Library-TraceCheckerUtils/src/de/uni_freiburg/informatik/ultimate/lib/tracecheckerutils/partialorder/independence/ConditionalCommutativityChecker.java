package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;


public class ConditionalCommutativityChecker<L extends IIcfgTransition<?>> {

	IPredicate mCondition;
	public ConditionalCommutativityChecker(IRun<L, IPredicate> run, IPredicate state, L a, L b, IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator, StrategyFactory<L> strategyFactory,
			final IUltimateServiceProvider services, final IAutomaton<L, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final IPredicateUnifier predicateUnifier, final RefinementStrategy strategyType) {
		
		if (Boolean.TRUE.equals(criterion.decide(state, a, b))) {
			IPredicate mCondition = generator.generateCondition(state, a.getTransformula(), b.getTransformula());
			if (Boolean.TRUE.equals(criterion.decide(mCondition))) {
				
				//construct strategy for nRun (= run + \neg condition) with precondition = true and postcondition = false
				ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(services, run, abstraction, taskIdentifier, emptyStackFactory,
						IPreconditionProvider.constructDefaultPreconditionProvider(), new CommutativityConditionProvider());
				if(strategy.nextFeasibilityCheck().isCorrect().equals(LBool.SAT)) {
					//condition holds after run
				}
			}
		}
	}
	
	private class CommutativityConditionProvider implements IPostconditionProvider{

		@Override
		public IPredicate constructPostcondition(IPredicateUnifier predicateUnifier) {
			predicateUnifier.getOrConstructPredicate(mCondition);
			return null;
		}
		
	}
}
