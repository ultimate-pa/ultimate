package local.stalin.SMTInterface.z3interpol;

import java.util.HashMap;
import java.util.Map;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.DistinctAtom;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;
import local.stalin.nativez3.Z3ProofRule;

public class InterpolationInfoHolder {
	public static class RangeHolder {
		private RangeHolder() {}
		public RangeHolder(int fn) {
			start = end = fn;
		}
		public RangeHolder combine(RangeHolder other) {
			if( other == null )
				return this;
			RangeHolder res = new RangeHolder();
			res.start = Math.max(start,other.start);
			res.end = Math.min(end,other.end);
			return res;
		}
		int start,end;
		public String toString() {
			return "[" + start + "," + end + "]";
		}
	}
	public final static class InterpolationException extends Exception {
		private static final long serialVersionUID = 6890239424391453964L;

		public InterpolationException(String msg) {
			super(msg);
		}
	}
	private final Theory mt;
	private final Formula[] mforms;
	// Key might be FunctionSymbol or PredicateSymbol
	private Map<Object,RangeHolder> mranges;
	
	private final void addRangeObject(Object obj,int fn) {
		RangeHolder rh = mranges.get(obj);
		if( rh == null ) {
			rh = new RangeHolder(fn);
			mranges.put(obj,rh);
		} else {
			if( rh.start > fn )
				rh.start = fn;
			if( rh.end < fn )
				rh.end = fn;
		}
	}
	
	private final void recinitterm(Term t,int fn) {
		addRangeObject(t, fn);
		if( t instanceof  ApplicationTerm ) {
			ApplicationTerm appterm = (ApplicationTerm)t;
			FunctionSymbol fs = appterm.getFunction();
			if( !fs.isIntern() )
				addRangeObject(fs, fn);
			Term[] params = appterm.getParameters();
			for( Term p : params )
				recinitterm(p, fn);
		} else if( t instanceof ITETerm ) {
			ITETerm ite = (ITETerm)t;
			recinitformula(ite.getCondition(), fn);
			recinitterm(ite.getTrueCase(), fn);
			recinitterm(ite.getFalseCase(), fn);
		}
	}
	
	private final void recinitformula(Formula f,int fn) {
		addRangeObject(f, fn);
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			recinitformula(conf.getLhs(), fn);
			recinitformula(conf.getRhs(), fn);
		} else if( f instanceof NegatedFormula ) {
			recinitformula(((NegatedFormula) f).getSubFormula(), fn);
		} else if( f instanceof EqualsAtom ) {
			EqualsAtom eqa = (EqualsAtom)f;
			Term[] terms = eqa.getTerms();
			for( Term t : terms )
				recinitterm(t, fn);
		} else if( f instanceof PredicateAtom ) {
			PredicateAtom pa = (PredicateAtom)f;
			PredicateSymbol ps = pa.getPredicate();
			if( !ps.isIntern() )
				addRangeObject(ps, fn);
			Term[] terms = pa.getParameters();
			for( Term t : terms )
				recinitterm(t, fn);
		} else if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			recinitformula(qf.getSubformula(), fn);
		} else if( f instanceof ITEFormula ) {
			ITEFormula ite = (ITEFormula)f;
			recinitformula(ite.getCondition(), fn);
			recinitformula(ite.getTrueCase(), fn);
			recinitformula(ite.getFalseCase(), fn);
		}
	}
	
	private final void initranges() {
		int i = -1;
		for( Formula f : mforms )
			recinitformula(f,++i);
	}
	
	public InterpolationInfoHolder(Theory t,Formula[] forms,boolean normalize) {
		mt = t;
		mforms = forms;
		mranges = new HashMap<Object, RangeHolder>();
		initranges();
	}
	
	public InterpolationInfoHolder(Theory t,Formula[] forms) {
		this(t,forms,false);
	}
	
	public final RangeHolder range(Formula f) throws InterpolationException {
		RangeHolder res = mranges.get(f);
		if( res == null )
			throw new InterpolationException("Unknown formula " + f.toString() + " in Interpolation");
		return res;
	}
	
	public final RangeHolder range(Object obj) throws InterpolationException {
		RangeHolder res = mranges.get(obj);
		if( res == null )
			throw new InterpolationException("Unknown symbol " + obj.toString() + " in Interpolation");
		return res;
	}
	public final RangeHolder termrange(Term t) throws InterpolationException {
		if( t instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)t;
			FunctionSymbol fs = at.getFunction();
			RangeHolder res = fs.isIntern() ? null : range(at.getFunction());
			Term[] params = at.getParameters();
			for( Term p : params )
				if( res != null )
					res = res.combine(termrange(p));
				else
					res = termrange(p);
			return res;
		}
		if( t instanceof ITETerm ) {
			ITETerm ite = (ITETerm)t;
			RangeHolder rh = symbolrange(ite.getCondition());
			RangeHolder tc = termrange(ite.getTrueCase());
			RangeHolder fc = termrange(ite.getFalseCase());
			if( rh == null )
				if( tc == null )
					return fc;
				else
					return tc.combine(fc);
			return rh.combine(tc).combine(fc);
		}
		return null;
	}
	/**
	 * Compute formula range based on symbols.
	 * @param f Formula to check
	 * @return <code>null</code> iff no symbol in formula
	 * @throws InterpolationException
	 */
	public final RangeHolder symbolrange(Formula f) throws InterpolationException {
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			RangeHolder res= symbolrange(conf.getLhs());
			RangeHolder r2 = symbolrange(conf.getRhs());
			return res == null ? r2 : r2 == null ? res : res.combine(r2);
		}
		if( f instanceof NegatedFormula )
			return symbolrange(((NegatedFormula)f).getSubFormula());
		if( f instanceof QuantifiedFormula )
			return symbolrange(((QuantifiedFormula)f).getSubformula());
		if( f instanceof ITEFormula ) {
			ITEFormula itef = (ITEFormula)f;
			RangeHolder res = symbolrange(itef.getCondition());
			RangeHolder tr = symbolrange(itef.getTrueCase());
			RangeHolder fc = symbolrange(itef.getFalseCase());
			if( res == null )
				if( tr != null)
					res = tr;
				else
					return fc;
			else
				res = res.combine(tr);
			return res.combine(fc);
		}
		if( f instanceof PredicateAtom ) {
			PredicateAtom pa = (PredicateAtom)f;
			PredicateSymbol ps = pa.getPredicate();
			RangeHolder res = ps.isIntern() ? null : range(ps);
			Term[] params = pa.getParameters();
			for( Term t : params ) {
				if( res == null )
					res = termrange(t);
				else
					res = res.combine(termrange(t));
			}
			return res;
		}
		if( f instanceof EqualsAtom ) {
			Term[] params = ((EqualsAtom)f).getTerms();
			RangeHolder res = null;
			for( Term t : params ) {
				RangeHolder tmp = termrange(t);
				if( res != null ) {
					if( tmp != null )
						res = res.combine(tmp);
				} else
					res = tmp;
			}
			return res;
		}
		if( f instanceof DistinctAtom ) {
			Term[] params = ((DistinctAtom)f).getTerms();
			RangeHolder res = null;
			for( Term t : params ) {
				RangeHolder tmp = termrange(t);
				if( res != null ) {
					if( tmp != null )
						res = res.combine(tmp);
				} else
					res = tmp;
			}
			return res;
		}
		return null;
	}
	public final Formula symbolRestrict2B(Formula f,int fn) throws InterpolationException {
		// OR and IMPLIES
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			if( conf.getConnector() == ConnectedFormula.OR )
				return mt.or(symbolRestrict2B(conf.getLhs(),fn),symbolRestrict2B(conf.getRhs(),fn));
			if( conf.getConnector() == ConnectedFormula.IMPLIES )
				return mt.or(symbolRestrict2B(mt.not(conf.getLhs()),fn),symbolRestrict2B(conf.getRhs(),fn));	
		}
		// NOT AND, NOT FORALL and double negation
		if( f instanceof NegatedFormula ) {
			Formula sub = ((NegatedFormula)f).getSubFormula();
			if( sub instanceof ConnectedFormula) {
				ConnectedFormula confsub = (ConnectedFormula)sub;
				if( confsub.getConnector() == ConnectedFormula.AND )
					return mt.or(symbolRestrict2B(mt.not(confsub.getLhs()),fn),symbolRestrict2B(mt.not(confsub.getRhs()),fn));
			} else if( sub instanceof QuantifiedFormula && ((QuantifiedFormula)sub).getQuantifier() == QuantifiedFormula.FORALL ) {
				QuantifiedFormula qf = (QuantifiedFormula)sub;
				return mt.exists(qf.getVariables(),symbolRestrict2B(mt.not(qf.getSubformula()),fn),qf.getTriggers());
			} else if( sub instanceof NegatedFormula )
				return symbolRestrict2B(((NegatedFormula)sub).getSubFormula(),fn);
		}
		// EXISTS
		if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			if( qf.getQuantifier() == QuantifiedFormula.EXISTS )
				return mt.exists(qf.getVariables(),symbolRestrict2B(qf.getSubformula(),fn),qf.getTriggers());
		}
		// Base case
		RangeHolder rh = symbolrange(f);
		if( rh != null && isB(rh,fn) )
			return f;
		return Atom.FALSE;
	}
	// Projection functions
	public final Formula restrict2B(Formula f,int fn) throws InterpolationException {
		// OR and IMPLIES
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			if( conf.getConnector() == ConnectedFormula.OR )
				return mt.or(restrict2B(conf.getLhs(),fn),restrict2B(conf.getRhs(),fn));
			if( conf.getConnector() == ConnectedFormula.IMPLIES )
				return mt.or(restrict2B(mt.not(conf.getLhs()),fn),restrict2B(conf.getRhs(),fn));	
		}
		// NOT AND, NOT FORALL and double negation
		else if( f instanceof NegatedFormula ) {
			Formula sub = ((NegatedFormula)f).getSubFormula();
			if( sub instanceof ConnectedFormula) {
				ConnectedFormula confsub = (ConnectedFormula)sub;
				if( confsub.getConnector() == ConnectedFormula.AND )
					return mt.or(restrict2B(mt.not(confsub.getLhs()),fn),restrict2B(mt.not(confsub.getRhs()),fn));
			} else if( sub instanceof QuantifiedFormula && ((QuantifiedFormula)sub).getQuantifier() == QuantifiedFormula.FORALL ) {
				QuantifiedFormula qf = (QuantifiedFormula)sub;
				return mt.exists(qf.getVariables(),restrict2B(mt.not(qf.getSubformula()),fn),qf.getTriggers());
			} else if( sub instanceof NegatedFormula )
				return restrict2B(((NegatedFormula)sub).getSubFormula(),fn);
		}
		// EXISTS
		else if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			if( qf.getQuantifier() == QuantifiedFormula.EXISTS )
				return mt.exists(qf.getVariables(),restrict2B(qf.getSubformula(),fn),qf.getTriggers());
			// Need this since QuantifiedFormula is not unified!!!
			return Atom.FALSE;
		}
		// Base case
		// Test with symbolrange
		RangeHolder rh = symbolrange(f);
		if( isB(rh,fn) )
			return f;
		return Atom.FALSE;
	}
	
	public final Formula withoutB(Formula f,int fn) throws InterpolationException {
		// OR and IMPLIES
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			if( conf.getConnector() == ConnectedFormula.OR )
				return mt.or(withoutB(conf.getLhs(),fn),withoutB(conf.getRhs(),fn));
			if( conf.getConnector() == ConnectedFormula.IMPLIES )
				return mt.or(withoutB(mt.not(conf.getLhs()),fn),withoutB(conf.getRhs(),fn));	
		}
		// NOT AND, NOT FORALL and double negation
		else if( f instanceof NegatedFormula ) {
			Formula sub = ((NegatedFormula)f).getSubFormula();
			if( sub instanceof ConnectedFormula) {
				ConnectedFormula confsub = (ConnectedFormula)sub;
				if( confsub.getConnector() == ConnectedFormula.AND )
					return mt.or(withoutB(mt.not(confsub.getLhs()),fn),withoutB(mt.not(confsub.getRhs()),fn));
			} else if( sub instanceof NegatedFormula )
				return withoutB(((NegatedFormula)sub).getSubFormula(),fn);
			else if( sub instanceof QuantifiedFormula && ((QuantifiedFormula)sub).getQuantifier() == QuantifiedFormula.FORALL ) {
				QuantifiedFormula qf = (QuantifiedFormula)sub;
				return mt.exists(qf.getVariables(),withoutB(mt.not(qf.getSubformula()),fn),qf.getTriggers());
			}
		}
		// EXISTS
		else if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			if( qf.getQuantifier() == QuantifiedFormula.EXISTS )
				return mt.exists(qf.getVariables(),withoutB(qf.getSubformula(),fn),qf.getTriggers());
			// Need this since QuantifiedFormula is not unified!!!
			return Atom.FALSE;
		}
		// Base case
		RangeHolder rh = range(f);
		if( isB(rh,fn) )
			return Atom.FALSE;
		return f;
	}
	// Membership tests
	public final boolean isB(RangeHolder rh,int fn) {
		return rh == null || rh.end > fn;
	}
	
	public final boolean isNotB(RangeHolder rh,int fn) {
		return rh.end <= fn;
	}
	
	public final Theory getSMTTheory() {
		return mt;
	}
	
	public final boolean isProjectionDistributive(Formula f) {
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			return conf.getConnector() == ConnectedFormula.OR || conf.getConnector() == ConnectedFormula.IMPLIES;
		}
		if( f instanceof NegatedFormula ) {
			NegatedFormula negf = (NegatedFormula)f;
			Formula sub = negf.getSubFormula();
			if( sub instanceof ConnectedFormula )
				return ((ConnectedFormula)sub).getConnector() == ConnectedFormula.AND;
			if( sub instanceof NegatedFormula )
				return isProjectionDistributive(((NegatedFormula)sub).getSubFormula());
		}
		if( f instanceof QuantifiedFormula )
			return ((QuantifiedFormula)f).getQuantifier() == QuantifiedFormula.EXISTS;
		return false;
	}
	public final Formula assumption(int assnum) {
		return mforms[assnum];
	}
	/**
	 * Update formula knowledge according to rewrite steps.
	 * 
	 * This function walk along the proof tree and updates the range maps
	 * whenever a rewrite step is encountered.
	 * @param proof Proof of Unsatisfiability produced by Z3
	 * @throws InterpolationException 
	 */
	public void update(Z3ProofRule proof) throws InterpolationException {
		if( proof.getRuleNumber() == Z3Interpolator.PR_QUANT_INTRO ) {
			// (iff asserted modified) or possibly (~ asserted modified)
			ConnectedFormula conf = (ConnectedFormula)proof.getResult();
			RangeHolder rh = mranges.get(conf.getLhs());
			System.err.println("Found range " + rh + " for " + conf.getLhs());
			mranges.put(conf.getRhs(),rh);
//		if( proof.getRuleNumber() == Z3Interpolator.PR_REWRITE || proof.getRuleNumber() == Z3Interpolator.PR_REWRITE_STAR ) {
//			System.err.println("Updating due to " + proof);
//			Formula res = proof.getResult();
//			if( res instanceof ConnectedFormula ) {
//				// (iff old new)
//				ConnectedFormula conf = (ConnectedFormula)res;
//				// Take care of assumptions marked with ass#
//				if( conf.getLhs() instanceof ConnectedFormula ) {
//					ConnectedFormula sub = (ConnectedFormula)conf.getLhs();
//					if( sub.getConnector() == ConnectedFormula.AND && ((ConnectedFormula)sub).getLhs() instanceof PredicateAtom ) {
//						PredicateAtom ass = (PredicateAtom)((ConnectedFormula)sub).getLhs();
//						PredicateSymbol ps = ass.getPredicate();
//						if( ps.getName().startsWith("ass") ) {
//							// Assumes predicate is ass<number>
//							int assnum = Integer.parseInt(ps.getName().substring(3));
//							mranges.put(conf.getRhs(),new RangeHolder(assnum));
//							return;
//						}
//					}
//				}
//				RangeHolder rh = range(conf.getLhs());
//				mranges.put(conf.getRhs(),rh);
//			} else {
//				// (= old new)
//				assert res instanceof EqualsAtom : "Unimplemented rewrite result";
//				EqualsAtom ea = (EqualsAtom)res;
//				RangeHolder rh = range(ea.getTerms()[0]);
//				mranges.put(ea.getTerms()[1],rh);
//			}
		}// else {
			Z3ProofRule[] antecedents = proof.getAntecedents();
			if( antecedents != null )
				for( Z3ProofRule pr : antecedents )
					update(pr);
//		}
	}
}
