package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

public class MonotonicityInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_MONOTONICITY] = this;
	}

	private final boolean allB(int num,Formula[] antecedents,InterpolationInfoHolder iih) throws InterpolationException {		
		for( int i = 0; i < antecedents.length; ++i ) {
			RangeHolder rh = iih.symbolrange(antecedents[i]);
			if( rh != null && iih.isNotB(rh,num) )
				return false;
		}
		return true;
	}
	
	private final boolean allNotB(int num,Formula[] antecedents,InterpolationInfoHolder iih) throws InterpolationException {		
		for( int i = 0; i < antecedents.length; ++i ) {
			RangeHolder rh = iih.symbolrange(antecedents[i]);
			if( iih.isB(rh,num) )
				return false;
		}
		return true;
	}
	
	private final Formula[] detectMissingReflexivities(Formula[] antecedents,Formula res) {
		// TODO: Implement!!!
		return new Formula[0];
	}
	
	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Theory t = iih.getSMTTheory();
		Interpolants result = new Interpolants(numforms);
		Formula[] mrp = detectMissingReflexivities(antecedents, res);
		for( int cn = 0; cn < numforms; ++cn ) {
			if( allB(cn, antecedents, iih) && allB(cn, mrp, iih) ) {
				Formula resip = Atom.TRUE;
				for( int i = 0; i < antecedents.length; ++i )
					resip = t.and(resip,antinterpols[i].getInterpolant(cn));
				result.setInterpolant(cn,resip);
				result.setSource(cn,Interpolants.DERIVATION_B);	
			} else if( allNotB(cn, antecedents, iih) && allNotB(cn, mrp, iih) ) {
				Formula resip = Atom.FALSE;
				for( int i = 0; i < antecedents.length; ++i )
					resip = t.or(resip,antinterpols[i].getInterpolant(cn));
				result.setInterpolant(cn,resip);
				result.setSource(cn,Interpolants.DERIVATION_A);
			} else
				throw new InterpolationInfoHolder.InterpolationException("AB-Mixed interpolation is not implemented!");
			//result.setSource(cn,Interpolants.DERIVATION_MIXED);
		}
		return result;
	}

}
