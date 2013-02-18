package local.stalin.SMTInterface.z3interpol;

import java.util.HashMap;
import java.util.Map;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.RangeHolder;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.DistinctAtom;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.VariableTerm;

public class TautologieInterpolationRule implements IInterpolationRule {

	private final void interpolateConf(Interpolants res,ConnectedFormula conf,InterpolationInfoHolder iih) throws InterpolationException {
		Formula lhs = conf.getLhs();
		RangeHolder rh = iih.symbolrange(lhs);
		for( int cn = 0; cn < res.getSize(); ++cn ) {
			if( iih.isB(rh,cn) )
				res.setInterpolant(cn, Atom.TRUE);
			else
				res.setInterpolant(cn,iih.symbolRestrict2B(conf,cn));
		}
	}
	
	private final int walkterm(Term sub,Term inst,int num,Map<TermVariable,Term> res) {
		if( num == 0 ) return 0;
		if( sub instanceof VariableTerm ) {
			if( inst instanceof VariableTerm )
				// Nested quantifier...
				return num;
			VariableTerm vt = (VariableTerm)sub;
			Term old = res.put(vt.getVariable(),inst);
			// TODO: Perhaps this check is not needed (Soundness of Z3)
			if( old != null && old != inst ) throw new IllegalArgumentException("Detected different instantiation");
			return num - 1;
		}
		if( sub instanceof ApplicationTerm ) {
			ApplicationTerm asub = (ApplicationTerm)sub;
			ApplicationTerm ainst = (ApplicationTerm)inst;
			assert(asub.getFunction() == ainst.getFunction());
			Term[] sparams = asub.getParameters();
			Term[] iparams = ainst.getParameters();
			assert(sparams.length == iparams.length);
			for( int i = 0; i < sparams.length && num > 0; ++i )
				num = walkterm(sparams[i],iparams[i],num,res);
			return num;
		}
		if( sub instanceof ITETerm ) {
			ITETerm isub = (ITETerm)sub;
			ITETerm iinst = (ITETerm)inst;
			num = walk(isub.getCondition(),iinst.getCondition(),num,res);
			num = walkterm(isub.getTrueCase(),iinst.getTrueCase(),num,res);
			return walkterm(isub.getFalseCase(),iinst.getFalseCase(),num,res);
		}
		return num;
	}
	
	private final int walk(Formula sub,Formula inst,int num,Map<TermVariable,Term> res) {
		if( num == 0 ) return 0;
		if( sub instanceof NegatedFormula ) {
			return walk(((NegatedFormula)sub).getSubFormula(),((NegatedFormula)inst).getSubFormula(),num,res);
		}
		if( sub instanceof ConnectedFormula ) {
			ConnectedFormula csub = (ConnectedFormula)sub;
			ConnectedFormula cinst = (ConnectedFormula)inst;
			num = walk(csub.getLhs(),cinst.getLhs(),num,res);
			return walk(csub.getRhs(),cinst.getRhs(),num,res);
		}
		if( sub instanceof QuantifiedFormula )
			return walk(((QuantifiedFormula)sub).getSubformula(),((QuantifiedFormula)inst).getSubformula(),num,res);
		if( sub instanceof ITEFormula ) {
			ITEFormula isub = (ITEFormula)sub;
			ITEFormula iinst = (ITEFormula)inst;
			num = walk(isub.getCondition(),iinst.getCondition(),num,res);
			num = walk(isub.getTrueCase(),iinst.getTrueCase(),num,res);
			return walk(isub.getFalseCase(),iinst.getFalseCase(),num,res);
		}
		if( sub instanceof PredicateAtom ) {
			PredicateAtom psub = (PredicateAtom)sub;
			PredicateAtom pinst = (PredicateAtom)inst;
			assert(psub.getPredicate() == pinst.getPredicate());
			Term[] sparams = psub.getParameters();
			Term[] iparams = pinst.getParameters();
			assert(sparams.length == iparams.length);
			for( int i = 0; i < iparams.length && num > 0; ++i )
				num = walkterm(sparams[i],iparams[i],num,res);
			return num;
		}
		if( sub instanceof EqualsAtom ) {
			Term[] sparams = ((EqualsAtom)sub).getTerms();
			Term[] iparams = ((EqualsAtom)inst).getTerms();
			assert(sparams.length == iparams.length);
			for( int i = 0; i < iparams.length && num > 0; ++i )
				num = walkterm(sparams[i],iparams[i],num,res);
			return num;
		}
		if( sub instanceof DistinctAtom ) {
			Term[] sparams = ((DistinctAtom)sub).getTerms();
			Term[] iparams = ((DistinctAtom)inst).getTerms();
			assert(sparams.length == iparams.length);
			for( int i = 0; i < iparams.length && num > 0; ++i )
				num = walkterm(sparams[i],iparams[i],num,res);
			return num;
		}
		if( sub == Atom.TRUE || sub == Atom.FALSE ) return num;
		throw new AssertionError("Unknown Formula type occured while searching for instantiations.");
	}
	
	private final Map<TermVariable,Term> findInstantiation(QuantifiedFormula qf,Formula inst) {
		int numbound = qf.getVariables().length;
		Map<TermVariable,Term> res = new HashMap<TermVariable,Term>(numbound);
		Formula sub = qf.getSubformula();
		walk(sub,inst,numbound,res);
		return res;
	}
	/**
	 * Computes ranges for instantiations.
	 * @param iih   Keeps range information
	 * @param insts Maps of instantiations
	 * @param ran   On return this map contains all ranges of corresponding instantiations
	 * @return Duration during which instantiations are in same partition
	 * @throws InterpolationException
	 */
	private final RangeHolder ranges(InterpolationInfoHolder iih,Map<TermVariable,Term> insts,Map<TermVariable,RangeHolder> ran) throws InterpolationException {
		RangeHolder res = null;
		for( Map.Entry<TermVariable,Term> me : insts.entrySet() ) {
			RangeHolder rh = iih.termrange(me.getValue());
			res = res == null ? rh : rh == null ? res : res.combine(rh);
			ran.put(me.getKey(),rh);
		}
		return res;
	}
	
	@Override
	public Interpolants interpolate(int numforms,int rule,Formula[] antecedents,
			Interpolants[] antinterpols,Formula res,InterpolationInfoHolder iih) throws InterpolationException{
		RangeHolder rh;
		Interpolants result = new Interpolants(numforms);
		switch( rule ) {
		case Z3Interpolator.PR_HYPOTHESIS:
			rh = iih.symbolrange(res);
			for( int cn = 0; cn < numforms; ++cn ) {
				if( iih.isB(rh,cn) )
					result.setInterpolant(cn,Atom.TRUE);
				else
					result.setInterpolant(cn,iih.symbolRestrict2B(res,cn));
			}
		case Z3Interpolator.PR_QUANT_INST:
			System.err.println("Quantifier Instantiation");
			// Check whether phi in forall x. phi(x) is shared...
			ConnectedFormula cf = (ConnectedFormula)res;
			QuantifiedFormula qf = (QuantifiedFormula)((NegatedFormula)(cf.getLhs())).getSubFormula();
			rh = iih.symbolrange(qf.getSubformula());
			RangeHolder qfr = iih.range(qf);
			for( int i = 0; i < numforms; ++i ) {
				if( rh.start <= i && i < rh.end ) {
					System.err.println("Instantiation of shared formula");
					Map<TermVariable,Term> insts = findInstantiation(qf, cf.getRhs());
					System.err.println(insts);
					Map<TermVariable,RangeHolder> ranges = new HashMap<TermVariable,RangeHolder>(insts.size());
					RangeHolder rh2 = ranges(iih,insts,ranges);
					if( rh2 == null || rh2.start <= i && i < rh2.end ) {
						// Shared instantiation
//						if( qfr.start <= i && i < qfr.end )
							// Formula is shared in this partition
							result.setInterpolant(i,cf.getRhs());
//						else if( iih.isB(qfr, i) )
//							result.setInterpolant(i,Atom.TRUE);
//						else
//							result.setInterpolant(i,Atom.FALSE);
					} else if( iih.isB(rh2,i) ) {
						// Instantiation from B
						if( iih.isB(qfr,i) )
							result.setInterpolant(i,Atom.TRUE);
						else
							result.setInterpolant(i,null/*TODO*/);
					} else {
						if( iih.isB(qfr,i) )
							result.setInterpolant(i,null/*TODO*/);
						else
							result.setInterpolant(i,Atom.FALSE);
					}
				} else
					throw new InterpolationException("Non-shared instantiation currently not implemented");
			}
			break;
		case Z3Interpolator.PR_REFLEXIVITY:
		case Z3Interpolator.PR_DISTRIBUTIVITY:
		case Z3Interpolator.PR_REWRITE:
		case Z3Interpolator.PR_PULL_QUANT:
		case Z3Interpolator.PR_PULL_QUANT_STAR:
		case Z3Interpolator.PR_PUSH_QUANT:
		case Z3Interpolator.PR_ELIM_UNUSED_VARS:
		case Z3Interpolator.PR_DER:
			
		case Z3Interpolator.PR_COMMUTATIVITY:
		case Z3Interpolator.PR_DEF_AXIOM:
		case Z3Interpolator.PR_SKOLEMIZE:
			// Check first subformula/subterm
			if( res instanceof EqualsAtom ) {
				EqualsAtom ea = (EqualsAtom) res;
				rh = iih.termrange(ea.getTerms()[0]);
				for( int cn = 0; cn < numforms; ++cn ) {
					if( rh == null || iih.isB(rh,cn) )
						result.setInterpolant(cn,Atom.TRUE);
					else
						result.setInterpolant(cn,iih.symbolRestrict2B(res,cn));
				}
			} else if( res instanceof ConnectedFormula ) {
				ConnectedFormula conf = (ConnectedFormula)res;
				interpolateConf(result, conf, iih);
			}
			break;
		}
		return result;
	}

	@Override
	public void install(IInterpolationRule[] repo) {
		repo[Z3Interpolator.PR_HYPOTHESIS] = this;
		repo[Z3Interpolator.PR_REFLEXIVITY] = this;
		repo[Z3Interpolator.PR_DISTRIBUTIVITY] = this;
		repo[Z3Interpolator.PR_REWRITE] = this;
		repo[Z3Interpolator.PR_PULL_QUANT] = this;
		repo[Z3Interpolator.PR_PULL_QUANT_STAR] = this;
		repo[Z3Interpolator.PR_PUSH_QUANT] = this;
		repo[Z3Interpolator.PR_ELIM_UNUSED_VARS] = this;
		repo[Z3Interpolator.PR_DER] = this;
		repo[Z3Interpolator.PR_QUANT_INST] = this;
		repo[Z3Interpolator.PR_COMMUTATIVITY] = this;
		repo[Z3Interpolator.PR_DEF_AXIOM] = this;
		repo[Z3Interpolator.PR_SKOLEMIZE] = this;
	}

}
