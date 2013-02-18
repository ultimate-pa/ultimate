package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Formula;

public class ElimInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_AND_ELIM] = this;
		repo[Z3Interpolator.PR_NOT_OR_ELIM] = this;
	}

	@Override
	public Interpolants interpolate(int numforms,int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Interpolants result = new Interpolants(numforms);
		for( int cn = 0; cn < numforms; ++cn ) {
			RangeHolder rh = iih.symbolrange(antecedents[0]);
			if( iih.isB(rh,cn) )
				result.setInterpolant(cn,antinterpols[0].getInterpolant(cn));
			else {
				rh = iih.symbolrange(res);
				if( iih.isNotB(rh,cn) )
					result.setInterpolant(cn,iih.getSMTTheory().or(antinterpols[0].getInterpolant(cn),iih.symbolRestrict2B(res,cn)));
				else
					throw new InterpolationInfoHolder.InterpolationException("AB-Mixed interpolation is not implemented");
			}
			result.setSource(cn,antinterpols[0].getSource(cn));
		}
		return result;
	}

}
