package local.stalin.SMTInterface.groundify;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Stack;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.DistinctAtom;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.FletFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.LetFormula;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableTerm;

public class QuantifierMarker {
	private int mnumquant = 0;
	private int mnumvars = 0;
	private Theory mtheory;
	private Map<Integer,QFRange> mnums,mbasemap;
	private Map<TermVariable,TermVariable> mtvdisambiguator;
	private LinkedList<Integer> mdepquants;
	private Sort mintsort;
	private boolean positive = true;
	/**
	 * Initialize marker.
	 * @param t         Theory used to generate and modify input.
	 * @param allocnums Mapping of formulae to allocation numbers.
	 */
	public QuantifierMarker(Theory t) {
		mtheory = t;
		mnums = mbasemap = new HashMap<Integer, QFRange>();
		mtvdisambiguator = new HashMap<TermVariable,TermVariable>();
		mdepquants = new LinkedList<Integer>();
		mintsort = t.getSort("Int");
//		if( mintsort == null )
//			mintsort = t.createSort("Int");
	}
	public void setAllocationMap(Map<Integer,QFRange> allocnums) {
		mnumquant = 0;
		mnums = allocnums;
		allocnums.putAll(mbasemap);
	}
	/*
	 * Z3 sometimes has problems with equally named bounded variables and proof
	 * trees. Hence I try to make them unique...
	 */
	public Formula markQuantifiers(Formula in,int fn) {
		if( in instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)in;
			TermVariable[] tvs = qf.getVariables();
			TermVariable[] ntvs = new TermVariable[tvs.length];
			for( int i = 0; i < tvs.length; ++i ) {
				ntvs[i] = mtheory.createTermVariable(tvs[i].getName()+"_"+(++mnumvars),tvs[i].getSort());
				mtvdisambiguator.put(tvs[i],ntvs[i]);
			}
			ArrayList<Sort> sorts = new ArrayList<Sort>();
			ArrayList<Term> args = new ArrayList<Term>();
			for( TermVariable tv : ntvs ) {
				sorts.add(tv.getSort());
				args.add(mtheory.term(tv));
			}
			for( Integer dep : mdepquants ) {
				sorts.add(mintsort);
				args.add(mtheory.numeral(BigInteger.valueOf(dep.longValue())));
				QFRange deprange = mnums.get(dep);
				TermVariable[] deptvs = deprange.qf.getVariables();
				for( TermVariable tv : deptvs ) {
					sorts.add(tv.getSort());
					args.add(mtheory.term(mtvdisambiguator.get(tv)));
				}
			}
			String predname = "quant"+mnumquant;
			Sort[] asorts = sorts.toArray(new Sort[sorts.size()]);
			PredicateSymbol ps = mtheory.createTempPredicate(predname, asorts);
			mnums.put(mnumquant,new QFRange(qf,fn));
			mdepquants.push(mnumquant);
			++mnumquant;
			Formula markedSub = markQuantifiers(qf.getSubformula(),fn);
			Formula marker = mtheory.atom(ps,args.toArray(new Term[args.size()]));
			Formula msub = positive ? mtheory.and(marker,markedSub) : mtheory.or(marker,markedSub);
			SMTLibBase[][] triggers = converttriggers(qf.getTriggers(),fn);
			for( TermVariable tv : tvs )
				mtvdisambiguator.remove(tv);
			mdepquants.pop();
			return qf.getQuantifier() == QuantifiedFormula.EXISTS ? 
					mtheory.exists(ntvs,msub,triggers) :
						mtheory.forall(ntvs,msub,triggers);
		} else if( in instanceof NegatedFormula ) {
			positive = !positive;
			Formula res = mtheory.not(markQuantifiers(((NegatedFormula)in).getSubFormula(),fn));
			positive = !positive;
			return res;
		} else if( in instanceof ConnectedFormula ) {
			Stack<Formula> parts = new Stack<Formula>();
			ConnectedFormula cf = (ConnectedFormula)in;
			int connector = cf.getConnector(); 
			if (connector == ConnectedFormula.IFF
				|| connector == ConnectedFormula.XOR){
				int oldnumquant = mnumquant;
				Formula lhs = markQuantifiers(cf.getLhs(),fn);
				/* Optimize repeated IFFs to prevent stack overflow. */
				// TODO: How to mark this????
//				while (cf.getRhs() instanceof ConnectedFormula
//						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
//					parts.push(lhs);
//					cf = (ConnectedFormula) cf.getRhs();
//					lhs = markQuantifiers(cf.getLhs(),fn);
//				}
//				// Small optimization: I do not push the last lhs
//				Formula rhs = markQuantifiers(cf.getRhs(),fn);
//				Formula res;
//				if (connector == ConnectedFormula.XOR) {
//					res = mtheory.xor(lhs, rhs);
//					while( !parts.isEmpty() )
//						res = mtheory.xor(parts.pop(), res);
//				} else {
//					res = mtheory.iff(lhs, rhs);
//					while( !parts.isEmpty() )
//						res = mtheory.iff(parts.pop(), res);
//				}
//				return res;
				Formula rhs = markQuantifiers(cf.getRhs(), fn);
				// If no quantifiers found, return original formula
				if (mnumquant == oldnumquant)
					return connector == ConnectedFormula.IFF ? mtheory.iff(lhs, rhs) : mtheory.xor(lhs, rhs);
				mnumquant = oldnumquant;
				Formula nlhs = markQuantifiers(mtheory.not(cf.getLhs()), fn);
				Formula nrhs = markQuantifiers(mtheory.not(cf.getRhs()), fn);
				return connector == ConnectedFormula.IFF ? 
						mtheory.or(mtheory.and(lhs,rhs),mtheory.and(nlhs,nrhs)) :
							mtheory.or(mtheory.and(lhs,nrhs),mtheory.and(nlhs,rhs));
			} else if (connector == ConnectedFormula.OR) {
				Formula lhs = markQuantifiers(cf.getLhs(),fn);
				/* Optimize repeated disjunctions to prevent stack overflow. */
				if (lhs == Atom.TRUE)
					return Atom.TRUE;
				parts.add(lhs);
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					cf = (ConnectedFormula) cf.getRhs();
					lhs = markQuantifiers(cf.getLhs(),fn);
					if (lhs == Atom.TRUE)
						return Atom.TRUE;
					parts.add(lhs);
				}
				Formula result = markQuantifiers(cf.getRhs(),fn);
				while (!parts.isEmpty()) {
					result = mtheory.or(parts.pop(), result);
				}
				return result;
			} else if (connector == ConnectedFormula.AND) {
				Formula lhs = markQuantifiers(cf.getLhs(),fn);
				/* Optimize repeated conjunctions to prevent stack overflow. */
				if (lhs == Atom.FALSE)
					return Atom.FALSE;
				parts.add(lhs);
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					cf = (ConnectedFormula) cf.getRhs();
					lhs = markQuantifiers(cf.getLhs(),fn);
					if (lhs == Atom.FALSE)
						return Atom.FALSE;
					parts.add(lhs);
				}
				Formula result = markQuantifiers(cf.getRhs(),fn);
				while (!parts.isEmpty()) {
					result = mtheory.and(parts.pop(),result);
				}
				return result;
			} else {
				assert(connector == ConnectedFormula.IMPLIES);
				positive = !positive;
				Formula lhs = markQuantifiers(cf.getLhs(),fn);
				positive = !positive;
				return mtheory.implies(lhs,markQuantifiers(cf.getRhs(),fn));
			}
		} else if (in instanceof ITEFormula) {
			ITEFormula ite = (ITEFormula)in;
			Formula mcond = markQuantifiers(ite.getCondition(),fn);
			Formula mtc = markQuantifiers(ite.getTrueCase(),fn);
			Formula mfc = markQuantifiers(ite.getFalseCase(),fn);
			return mcond == ite.getCondition() && mtc == ite.getTrueCase() && mfc == ite.getFalseCase() ? 
					ite : mtheory.ifthenelse(mcond,mtc,mfc);
		} else if( in instanceof FletFormula ) {
			FletFormula flet = (FletFormula)in;
			Formula mval = markQuantifiers(flet.getValue(),fn);
			Formula msub = markQuantifiers(flet.getSubFormula(),fn);
			return mtheory.flet(flet.getVariable(),mval,msub);
		} else if( in instanceof LetFormula ) {
			LetFormula let = (LetFormula)in;
			return mtheory.let(let.getVariable(),convertterm(let.getValue(),fn),markQuantifiers(let.getSubFormula(),fn));
		} else if( in instanceof PredicateAtom ) {
			PredicateAtom pa = (PredicateAtom)in;
			Term[] params = pa.getParameters();
			Term[] nparams = new Term[params.length];
			for( int k = 0; k < params.length; ++k )
				nparams[k] = convertterm(params[k],fn);
			return mtheory.atom(pa.getPredicate(),nparams);
		} else if( in instanceof EqualsAtom ) {
			EqualsAtom ea = (EqualsAtom)in;
			Term[] params = ea.getTerms();
			Term[] nparams = new Term[params.length];
			for( int i = 0; i < params.length; ++i )
				nparams[i] = convertterm(params[i],fn);
			return mtheory.equals(nparams);
		} else if( in instanceof DistinctAtom ) {
			DistinctAtom ea = (DistinctAtom)in;
			Term[] params = ea.getTerms();
			Term[] nparams = new Term[params.length];
			for( int i = 0; i < params.length; ++i )
				nparams[i] = convertterm(params[i],fn);
			return mtheory.distinct(nparams);
		} 
		return in;
	}
	private SMTLibBase[][] converttriggers(SMTLibBase[][] triggers,int fn) {
		SMTLibBase[][] res = new SMTLibBase[triggers.length][];
		for( int i = 0; i < triggers.length; ++i ) {
			SMTLibBase[] trigs = triggers[i];
			SMTLibBase[] ntrigs = new SMTLibBase[trigs.length];
			for( int j = 0; j < trigs.length; ++j ) {
				SMTLibBase trigger = trigs[j];
				if( trigger instanceof PredicateAtom ) {
					PredicateAtom pa = (PredicateAtom)trigger;
					Term[] params = pa.getParameters();
					Term[] nparams = new Term[params.length];
					for( int k = 0; k < params.length; ++k )
						nparams[k] = convertterm(params[k],fn);
					ntrigs[j] = mtheory.atom(pa.getPredicate(),nparams);
				} else
					ntrigs[j] = convertterm((Term)trigger,fn);
			}// End converting one trigger array
			res[i] = ntrigs;
		}
		return res;
	}
	private Term convertterm(Term term,int fn) {
		if( term instanceof ITETerm ) {
			ITETerm itet = (ITETerm)term;
			Formula cond = markQuantifiers(itet.getCondition(),fn);
			Term tc = convertterm(itet.getTrueCase(),fn);
			Term fc = convertterm(itet.getFalseCase(),fn);
			return mtheory.ite(cond,tc,fc);
		} else if( term instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)term;
			Term[] params = at.getParameters();
			Term[] nparams = new Term[params.length];
			for( int i = 0; i < params.length; ++i )
				nparams[i] = convertterm(params[i],fn);
			return mtheory.term(at.getFunction(),nparams);
		} else if( term instanceof VariableTerm ) {
			TermVariable tv = ((VariableTerm)term).getVariable();
			TermVariable ntv = mtvdisambiguator.get(tv);
			return ntv == null ? /* Let bound */term : mtheory.term(ntv);
		}
		return term;
	}
}
