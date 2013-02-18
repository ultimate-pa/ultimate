package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

public class ResolutionInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_UNIT_RESOLUTION] = this;
	}

	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Interpolants result = new Interpolants(antinterpols[0].getInterpolants());
		Theory t = iih.getSMTTheory();
//		for( int cn = 0; cn < numforms; ++cn )
//			result[cn] = antinterpols[0][cn];
		for( int i = 0; i < antecedents.length; ++i ) {
			RangeHolder rh = iih.symbolrange(antecedents[i]);
			for( int cn = 0; cn < numforms; ++cn ) {
				if( iih.isB(rh,cn) )
					result.setInterpolant(cn,t.and(result.getInterpolant(cn),antinterpols[i].getInterpolant(cn)));
				else
					result.setInterpolant(cn,t.or(result.getInterpolant(cn),antinterpols[i].getInterpolant(cn)));
				result.setSource(cn,result.getSource(cn) | antinterpols[i].getSource(cn));
			}
		}
		return result;
	}

}
