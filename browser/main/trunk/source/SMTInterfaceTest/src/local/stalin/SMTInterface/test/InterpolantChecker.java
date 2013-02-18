package local.stalin.SMTInterface.test;

import java.util.HashMap;
import java.util.Map;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;

public class InterpolantChecker {
	private static class RangeHolder {
		public RangeHolder(int fn) {
			start = end = fn;
		}
		int start,end;
	}
	// Key might be FunctionSymbol or PredicateSymbol
	private Map<Object,RangeHolder> mranges;
	private Formula[] mforms;
	private Theory mtheory;
	private SMTInterface miface;
	
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
		FormulaUnFleterer unflet = new FormulaUnFleterer(mtheory);
		for (Formula axiom : mtheory.getAxioms())
			recinitformula(unflet.unflet(axiom), i);
		for( Formula f : mforms )
			recinitformula(unflet.unflet(f),++i);
	}
	
	private final void checkRange(Formula ipl,Object obj,int inum) throws IncorrectInterpolantException {
		RangeHolder rh = mranges.get(obj);
		if( rh == null )
			throw new IncorrectInterpolantException(ipl,"Symbol " + obj.toString() + " does not exist in input");
		if (rh.start == -1)
			// Theory extension
			return;
		if( !(rh.start <= inum && inum < rh.end) )
			throw new IncorrectInterpolantException(ipl,"Symbol " + obj.toString() + " is not shared");
	}
	
	private final void checkvarsformula(Formula ipl,Formula f,int inum) throws IncorrectInterpolantException {
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			checkvarsformula(ipl,conf.getLhs(), inum);
			checkvarsformula(ipl,conf.getRhs(),inum);
		} else if( f instanceof NegatedFormula ) {
			checkvarsformula(ipl,((NegatedFormula) f).getSubFormula(),inum);
		} else if( f instanceof EqualsAtom ) {
			EqualsAtom eqa = (EqualsAtom)f;
			Term[] terms = eqa.getTerms();
			for( Term t : terms )
				checkvarsterm(ipl,t,inum);
		} else if( f instanceof PredicateAtom ) {
			PredicateAtom pa = (PredicateAtom)f;
			PredicateSymbol ps = pa.getPredicate();
			if( !ps.isIntern() )
				checkRange(ipl, ps, inum);
			Term[] terms = pa.getParameters();
			for( Term t : terms )
				checkvarsterm(ipl, t, inum);
		} else if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			checkvarsformula(ipl, qf.getSubformula(), inum);
		} else if( f instanceof ITEFormula ) {
			ITEFormula ite = (ITEFormula)f;
			checkvarsformula(ipl, ite.getCondition(), inum);
			checkvarsformula(ipl, ite.getTrueCase(), inum);
			checkvarsformula(ipl, ite.getFalseCase(), inum);
		}
	}
	
	private final void checkvarsterm(Formula ipl,Term t,int inum) throws IncorrectInterpolantException {
		if( t instanceof  ApplicationTerm ) {
			ApplicationTerm appterm = (ApplicationTerm)t;
			FunctionSymbol fs = appterm.getFunction();
			if( !fs.isIntern() )
				checkRange(ipl, fs, inum);
			Term[] params = appterm.getParameters();
			for( Term p : params )
				checkvarsterm(ipl, p, inum);
		} else if( t instanceof ITETerm ) {
			ITETerm ite = (ITETerm)t;
			checkvarsformula(ipl, ite.getCondition(), inum);
			checkvarsterm(ipl, ite.getTrueCase(), inum);
			checkvarsterm(ipl, ite.getFalseCase(), inum);
		}
	}
	
	private final Formula createA(int fnum) {
		Formula res = Atom.TRUE;
		for( int i = 0; i <= fnum; ++i )
			res = mtheory.and(res,mforms[i]);
		return res;
	}
	
	private final Formula createB(int fnum) {
		Formula res = Atom.TRUE;
		for( int i = fnum + 1; i < mforms.length; ++i )
			res = mtheory.and(res,mforms[i]);
		return res;
	}
	
	public InterpolantChecker(Theory t,Formula[] forms) {
		mforms = forms;
		mranges = new HashMap<Object,RangeHolder>();
		mtheory = t;
		initranges();
		miface = new SMTInterface(t,SMTInterface.SOLVER_Z3_NATIVE);
	}

	public void checkInterpolants(Formula[] interpolants) throws IncorrectInterpolantException {
		for( int i = 0; i < interpolants.length; ++i ) {
			Formula f = interpolants[i];
			assert(f.typeCheck());
			// Check shared symbol condition
			checkvarsformula(f,f,i);
			// Check A=>I is tautologie
			Formula a = createA(i);
			assert(a.typeCheck());
			Formula checka = mtheory.not(mtheory.implies(a,f));
			assert(checka.typeCheck());
			System.err.println("A=>I: " + checka);
			if( miface.checkSatisfiable(checka) != SMTInterface.SMT_UNSAT )
				throw new IncorrectInterpolantException(f,"Not tautologically implied by A");
			// Check B&&I is unsat
			Formula b = createB(i);
			assert(b.typeCheck());
			Formula checkb = mtheory.and(b,f);
			assert(checkb.typeCheck());
			System.err.println("B&&I: " + checkb);
			if( miface.checkSatisfiable(checkb) != SMTInterface.SMT_UNSAT )
				throw new IncorrectInterpolantException(f,"Conjunction with B is satisfiable");
			System.err.println("Interpolant " + f + " is correct");
		}
	}
	
	@Override
	protected void finalize() throws Throwable {
		miface.close();
		super.finalize();
	}
	
	static class IncorrectInterpolantException extends Exception {
		/**
		 * 
		 */
		private static final long serialVersionUID = 1330795552582625762L;
		private final Formula mipl;
		private final String mreason;
		public IncorrectInterpolantException(Formula ipl,String reason) {
			mipl = ipl;
			mreason = reason;
		}
		@Override
		public String getMessage() {
			StringBuilder sb = new StringBuilder();
			sb.append("Interpolant ").append(mipl).append(" is incorrect: ").append(mreason);
			return sb.toString();
		}
	}
}
