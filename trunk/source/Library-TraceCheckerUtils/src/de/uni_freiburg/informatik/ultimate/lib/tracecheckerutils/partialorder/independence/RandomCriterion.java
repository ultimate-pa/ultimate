package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import java.util.Random;

public class RandomCriterion<L extends IIcfgTransition<?>> implements IConditionalCommutativityCriterion<L> {
	 
	private double mProbability;
	private Random mRandomGenerator;
	
	public RandomCriterion(double probability, long seed) {
		mProbability = probability;
		mRandomGenerator = new Random(seed);
	}
	
	@Override
	public Boolean decide(IPredicate state, L a, L b) {

		return (mRandomGenerator.nextInt(100)/100) < mProbability;
	}
	
	@Override
	public Boolean decide(IPredicate condition) {
		return true;
	}

}
