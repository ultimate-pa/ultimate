package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;


public class ConditionalCommutativityCriterionChecker<L extends IIcfgTransition<?>> {

	private IPredicate mCondition;
	private IConditionalCommutativityCriterion<L> mCriterion;
	private SemanticIndependenceConditionGenerator mGenerator;
	public ConditionalCommutativityCriterionChecker(IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator) {
		mCriterion = criterion;
		mGenerator = generator;
		/*
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
		}*/
	}
	
	public IPredicate getCondition(IRun<L, IPredicate> run, IPredicate state, L a, L b) {
		IPredicate condition = null;
		if (Boolean.TRUE.equals(mCriterion.decide(state, a, b))) {
			condition = mGenerator.generateCondition(state, a.getTransformula(), b.getTransformula());
		}
		return condition;
	}
	
	public Boolean checkCondition() {
		return Boolean.TRUE.equals(mCriterion.decide(mCondition));
	}
}
