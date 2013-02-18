package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;

public class AssertionInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_ASSERTED] = this;
		repo[Z3Interpolator.PR_GOAL] = this;
	}
	
	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Interpolants result = new Interpolants(numforms);
//		RangeHolder rh = iih.range(res);
//		for( int cn = 0; cn < numforms; ++cn ) {
//			if( iih.isB(rh,cn) ) {
//				result.setInterpolant(cn,Atom.TRUE);
//				result.setSource(cn,Interpolants.DERIVATION_B);
//			} else {
//				result.setInterpolant(cn,iih.restrict2B(res,cn));
//				result.setSource(cn,Interpolants.DERIVATION_A);
//			}
//		}
		if(res instanceof ConnectedFormula) {
			assert(res.typeCheck());
			ConnectedFormula conf = (ConnectedFormula)res;
			assert(conf.getConnector() == ConnectedFormula.AND);
			Formula lhs = conf.getLhs();
			assert(lhs instanceof PredicateAtom);
			PredicateAtom pa = (PredicateAtom)lhs;
			PredicateSymbol ps = pa.getPredicate();
			// Assumes predicate is ass<number>
			int assnum = Integer.parseInt(ps.getName().substring(3));
			Formula realass = iih.assumption(assnum);
			Formula rhs = ((ConnectedFormula)realass).getRhs();
			int cn = 0;
			//int end = Math.min(assnum,result.getSize()-1);
			for( ; cn < assnum; ++cn ) {
				result.setInterpolant(cn,Atom.TRUE);
				result.setSource(cn,Interpolants.DERIVATION_B);
			}
			for( ; cn < result.getSize(); ++cn ) {
				result.setInterpolant(cn,iih.restrict2B(rhs,cn));
				result.setSource(cn,Interpolants.DERIVATION_A);
			}
			return result;
		}
		for( int i = 0; i < result.getSize(); ++i ) {
			result.setInterpolant(i,Atom.TRUE);
			result.setSource(i,Interpolants.DERIVATION_UNKNOWN);
		}
		return result;
	}

}
