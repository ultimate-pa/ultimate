package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;

public class NNFInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_NNF_NEG] = this;
		repo[Z3Interpolator.PR_NNF_POS] = this;
	}

	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		RangeHolder rh = iih.symbolrange(res);
		Interpolants result = new Interpolants(numforms);
		for( int cn = 0; cn < numforms; ++cn ) {
			if( iih.isB(rh,cn) )
				result.setInterpolant(cn,Atom.TRUE);
			else
				result.setInterpolant(cn,Atom.FALSE);
		}
		return result;
	}

}
