package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

public class MPInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_MODUS_PONENS] = this;
		repo[Z3Interpolator.PR_MODUS_PONENS_OEQ] = this;
	}

	@Override
	public Interpolants interpolate(int numformulas, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Interpolants result = new Interpolants(numformulas);
		Theory t = iih.getSMTTheory();
		ConnectedFormula conf = (ConnectedFormula)antecedents[1];
		RangeHolder rh = null;
		boolean isB = false;
		switch( conf.getConnector() ) {
		case ConnectedFormula.IMPLIES:
			// antinterpols[0] == I_f, antinterpols[1] == I_{f\rightarrow G}
//			rh = iih.symbolrange(antecedents[0]);
			try {
				rh = iih.range(antecedents[0]);
			} catch(InterpolationException ie) {
				isB = true;
			}
			for( int cn = 0; cn < numformulas; ++cn ) {
				if( isB || iih.isB(rh,cn) )
					result.setInterpolant(cn,t.and(antinterpols[1].getInterpolant(cn),antinterpols[0].getInterpolant(cn)));
				else if( iih.isProjectionDistributive(antecedents[0]) )
					result.setInterpolant(cn,t.or(t.and(antinterpols[0].getInterpolant(cn),iih.symbolRestrict2B(antecedents[0],cn)),antinterpols[1].getInterpolant(cn)));
				else
					result.setInterpolant(cn,t.or(antinterpols[0].getInterpolant(cn),t.and(antinterpols[1].getInterpolant(cn),t.not(iih.symbolRestrict2B(t.not(antecedents[0]),cn)))));
				result.setSource(cn,antinterpols[0].getSource(cn) | antinterpols[1].getSource(cn));
			}
			return result;
		case ConnectedFormula.IFF:
		case ConnectedFormula.OEQ:
//			rh = iih.symbolrange(conf);
			try {
				rh = iih.range(antecedents[0]);
			} catch(InterpolationException ie) {
				isB = true;
			}
			for( int cn = 0; cn < numformulas; ++cn ) {
				if( isB || iih.isB(rh,cn) )
					result.setInterpolant(cn,t.and(antinterpols[1].getInterpolant(cn),antinterpols[0].getInterpolant(cn)));
				else {
					// equivalence not in B
					RangeHolder rh2 = iih.symbolrange(antecedents[0]);
					if( iih.isB(rh2,cn) )
//						throw new InterpolationInfoHolder.InterpolationException("AB-mixed interpolation not implemented!");
						result.setInterpolant(cn,t.or(antinterpols[0].getInterpolant(cn),t.and(antinterpols[1].getInterpolant(cn),antecedents[0])));
					if( iih.isProjectionDistributive(antecedents[0]) )
						result.setInterpolant(cn,t.or(t.or(t.and(antinterpols[0].getInterpolant(cn),iih.symbolRestrict2B(antecedents[0],cn)),antinterpols[1].getInterpolant(cn)),iih.symbolRestrict2B(res,cn)));
					else
						result.setInterpolant(cn,t.or(antinterpols[0].getInterpolant(cn),t.and(t.or(antinterpols[1].getInterpolant(cn),iih.symbolRestrict2B(res,cn)),t.not(iih.symbolRestrict2B(t.not(antecedents[0]),cn)))));
				}
				result.setSource(cn,antinterpols[0].getSource(cn) | antinterpols[1].getSource(cn));
			}
			return result;
		}
		throw new InterpolationInfoHolder.InterpolationException("MPInterpolationRule does not support rule " + rule);
	}

}
