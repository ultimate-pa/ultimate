package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

public class TransInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_TRANSITIVITY] = this;
	}

	@Override
	public Interpolants interpolate(int num, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Theory t = iih.getSMTTheory();
		RangeHolder rh1 = iih.symbolrange(antecedents[0]);
		RangeHolder rh2 = iih.symbolrange(antecedents[1]);
		RangeHolder rh3 = iih.symbolrange(res);
		Interpolants result = new Interpolants(num);
		for( int cn = 0; cn < num; ++cn ) {
			if( iih.isB(rh1,cn) && iih.isB(rh2,cn) )
				result.setInterpolant(cn,t.and(antinterpols[0].getInterpolant(cn),antinterpols[1].getInterpolant(cn)));
			else if( iih.isNotB(rh1,cn) && iih.isNotB(rh2,cn) ) {
				result.setInterpolant(cn,t.or(antinterpols[0].getInterpolant(cn),antinterpols[1].getInterpolant(cn)));
				if( iih.isB(rh3,cn) )
					// TODO: Check whether res or iih.restrict2B(res,cn) should be used.
					result.setInterpolant(cn,t.or(result.getInterpolant(cn),res));
			} else
				throw new InterpolationInfoHolder.InterpolationException("AB-Mixed interpolation is not implemented!");
			result.setSource(cn,antinterpols[0].getSource(cn) | antinterpols[1].getSource(cn));
		}
		return result;
	}

}
