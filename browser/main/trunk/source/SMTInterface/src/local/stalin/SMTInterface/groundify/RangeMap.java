package local.stalin.SMTInterface.groundify;

import java.util.HashMap;
import java.util.Map;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.RationalTerm;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.smt.hack.SymbolRange;

class RangeMap implements FormulaWalker.SymbolVisitor {
	private Map<PredicateSymbol,SymbolRange> mpredranges;
	private Map<FunctionSymbol,SymbolRange> mfuncranges;
	private Theory mtheory;
	private int curnum;
	private SymbolRange currange;
	public RangeMap(Theory theory) {
		mpredranges = new HashMap<PredicateSymbol, SymbolRange>();
		mfuncranges = new HashMap<FunctionSymbol, SymbolRange>();
		mtheory = theory;
	}
	public void generateRanges(Formula[] forms) {
		FormulaWalker fwalker = new FormulaWalker(this,mtheory);
		currange = new SymbolRange(SymbolRange.THEORYEXTENSION);
		currange.last = forms.length;
		for( Formula ax: mtheory.getAxioms() )
			fwalker.process(ax);
		for( int i = 0; i < forms.length; ++i ) {
			currange = new SymbolRange(i);
			curnum = i;
			fwalker.process(forms[i]);
		}
	}
	@Override
	public void endscope(TermVariable tv) {}
	@Override
	public void endscopes(TermVariable[] tvs) {}
	@Override
	public void let(TermVariable tv, Term mval) {
		term(mval);
	}
	@Override
	public Formula predicate(PredicateAtom pa) {
		PredicateSymbol ps = pa.getPredicate();
		if( !ps.isIntern() ) {
			SymbolRange sr = mpredranges.get(ps);
			if( sr == null )
				mpredranges.put(ps,new SymbolRange(currange));
			else
				sr.update(curnum);
		}
		return null;
	}
	@Override
	public void quantifier(TermVariable[] tvs) {}
	@Override
	public Term term(Term input) {
		if( input instanceof ApplicationTerm ) {
			ApplicationTerm app = (ApplicationTerm)input;
			FunctionSymbol fs = app.getFunction();
			if( !fs.isIntern() )
				updatefs(fs);
			return null;
		} else if( input instanceof ITETerm )
			return null;
		return input;
	}
	@Override
	public boolean unflet() {
		return false;
	}
	@Override
	public boolean unlet() {
		return false;
	}
	private final void updatefs(FunctionSymbol fs) {
		SymbolRange sr = mfuncranges.get(fs);
		if( sr == null )
			mfuncranges.put(fs,new SymbolRange(currange));
		else
			sr.update(curnum);
	}
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for( Map.Entry<PredicateSymbol,SymbolRange> me : mpredranges.entrySet() )
			sb.append(me.getKey().getName()).append("->").append(me.getValue());
		for( Map.Entry<FunctionSymbol,SymbolRange> me : mfuncranges.entrySet() )
			sb.append(me.getKey().getName()).append("->").append(me.getValue());
		return sb.toString();
	}
	public SymbolRange range(PredicateSymbol ps) {
		return mpredranges.get(ps);
	}
	public SymbolRange range(FunctionSymbol fs) {
		return mfuncranges.get(fs);
	}
	public SymbolRange range(Term t) {
		if( t instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)t;
			Term[] args = at.getParameters();
			SymbolRange frange = range(at.getFunction());
			for( Term arg : args )
				frange = frange == null ? range(arg) : frange.combine(range(arg));
			return frange;
		}
		if( t instanceof NumeralTerm || t instanceof RationalTerm )
			return new SymbolRange(SymbolRange.THEORYEXTENSION);
		throw new UnsupportedOperationException("Unknown term class in range: " + t.getClass());
	}
	@Override
	public void done(Term input) {}
	@Override
	public void done(PredicateAtom pa) {}
	public final void skolemFunction(FunctionSymbol fs,int assnum) {
		mfuncranges.put(fs,new SymbolRange(assnum));
	}
}
