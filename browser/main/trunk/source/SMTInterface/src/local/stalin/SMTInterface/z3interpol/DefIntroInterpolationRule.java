package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.logic.Formula;

public class DefIntroInterpolationRule implements IInterpolationRule {
	
	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_DEF_INTRO] = this;
	}

	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		throw new InterpolationInfoHolder.InterpolationException("DEF_INTRO is not implemented yet!");
	}

}
