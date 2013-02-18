package local.stalin.SMTInterface.z3interpol;

import java.util.Arrays;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.smt.convert.ConvertFormula;
import local.stalin.smt.dpll.DPLLEngine;

public class TInterpolationRule implements IInterpolationRule {

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_TH_LEMMA] = this;
	}

	@Override
	public Interpolants interpolate(int numforms, int rule, Formula[] antecedents,
			Interpolants[] antinterpols, Formula res, InterpolationInfoHolder iih)
			throws InterpolationException {
		Formula[] ass = new Formula[numforms+1];
		Theory t = iih.getSMTTheory();
		DPLLEngine engine = new DPLLEngine(t,null);
		ConvertFormula cf = new ConvertFormula(engine);
		for( int i = 0; i <= numforms; ++i )
			ass[i] = Atom.TRUE;
		Formula mixed = Atom.TRUE;
		// TODO: Add formulae according to DERIVATION_A or DERIVATION_B flag
		for( int j = 0; j < antecedents.length; ++j ) {
			Formula f = antecedents[j];
			if( antinterpols[j].getSource(0) == Interpolants.DERIVATION_A ) {
				// This means, formula is derived from assumption 0
				ass[0] = t.and(ass[0],f);
			} else if( antinterpols[j].getSource(0) == Interpolants.DERIVATION_B ) {
				// This means, assumption was somewhere later. Search this point.
				int assnum = antinterpols[j].getSourceChangeIdx();
				ass[assnum] = t.and(ass[assnum],f);
			} else {
				RangeHolder rh = iih.symbolrange(f);
				for( int i = rh.start; i <= rh.end; ++i )
					ass[i] = t.and(ass[i],f);
				if( rh.start > rh.end )
					mixed = t.and(mixed,f);
			}
		}
		if( res != Atom.FALSE ) {
			RangeHolder rh = iih.symbolrange(res);
			if( rh.start > rh.end )
				return Interpolants.createInterpolants(Atom.FALSE,numforms);
			Formula nres = t.not(res);
			assert rh != null : "Could not find symbolrange for " + res;
			for( int i = rh.start; i <= rh.end; ++i )
				ass[i] = t.and(ass[i],nres);
		}
		if( mixed != Atom.FALSE && mixed != Atom.TRUE) {
			System.err.println("Adding mixed formula " + mixed);
			cf.addNOFormula(mixed);
		}
		System.err.println("Converting formulae");
		for( Formula f : ass ) {
			System.err.println(f);
			cf.addFormula(f);
		}
		cf.close();
		boolean sat = engine.solve();
		assert !sat : "Non-tautology as T-lemma: " + Arrays.toString(antecedents) + " --> " + res;
		Formula[] result = engine.getInterpolants();
		System.err.println("Interpolants: " + Arrays.toString(result));
		return new Interpolants(result);
	}

}
