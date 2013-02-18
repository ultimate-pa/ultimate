package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.logic.Formula;

public class KeepInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_SYMMETRY] = this;
		repo[Z3Interpolator.PR_QUANT_INTRO] = this;
		repo[Z3Interpolator.PR_LEMMA] = this;
		repo[Z3Interpolator.PR_IFF_TRUE] = this;
		repo[Z3Interpolator.PR_IFF_FALSE] = this;
		repo[Z3Interpolator.PR_APPLY_DEF] = this;
		repo[Z3Interpolator.PR_IFF_OEQ] = this;
	}

	@Override
	public Interpolants interpolate(int numforms,int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		return antinterpols[0];
	}

}
