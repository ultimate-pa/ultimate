package local.stalin.smt.dpll;

import java.util.HashMap;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;

public class Substitute {
	private static Term[] recReplace(DPLLEngine engine,Term[] terms,boolean eq,NOEqMap nomap) {
		Term[] res = new Term[terms.length];
		for( int i = 0; i < terms.length; ++i ) {
			Term t = terms[i];
			Term subst = nomap.get(t);
			if( subst != null )
				res[i] = subst;
			else if( t instanceof  ApplicationTerm ) {
				ApplicationTerm appterm = (ApplicationTerm)t;
				FunctionSymbol fs = appterm.getFunction();
				Term[] args = recReplace(engine,appterm.getParameters(),false,nomap);
				res[i] = engine.getSMTTheory().term(fs,args);
			} else if( t instanceof ITETerm ) {
				ITETerm ite = (ITETerm)t;
				Formula cond = recReplace(engine,ite.getCondition(),nomap);
				Term thenf = recReplace(engine,new Term[]{ite.getTrueCase()},false,nomap)[0];
				Term elsef = recReplace(engine,new Term[]{ite.getFalseCase()},false,nomap)[0];
				res[i] = engine.getSMTTheory().ite(cond,thenf,elsef);
			} else
				res[i] = t;
		}
		return res;
	}
	private static Formula recReplace(DPLLEngine engine,Formula f,NOEqMap nomap) {
		if( f instanceof ConnectedFormula ) {
			ConnectedFormula conf = (ConnectedFormula)f;
			int connector = conf.getConnector();
			Formula rlhs = recReplace(engine,conf.getLhs(),nomap);
			Formula rrhs = recReplace(engine,conf.getRhs(),nomap);
			switch( connector ) {
			case ConnectedFormula.AND:
				return engine.andFormula(rlhs,rrhs);
			case ConnectedFormula.OR:
				return engine.orFormula(rlhs,rrhs);
			case ConnectedFormula.IMPLIES:
				return engine.implFormula(rlhs,rrhs);
			default:
				throw new IllegalArgumentException("Connections other than AND, OR or IMPLIES should not occur in interpolant!");
			}
		} else if( f instanceof NegatedFormula ) {
			NegatedFormula negf = (NegatedFormula)f;
			Formula simpPos = recReplace(engine,negf.getSubFormula(),nomap);
			return engine.getSMTTheory().not(simpPos);
		} else if( f instanceof EqualsAtom ) {
			EqualsAtom eqa = (EqualsAtom)f;
			Term[] terms = recReplace(engine,eqa.getTerms(),true,nomap);
			return terms == null ? Atom.TRUE : engine.getSMTTheory().equals(terms);
		} else if( f instanceof PredicateAtom ) {
			PredicateAtom pa = (PredicateAtom)f;
			PredicateSymbol ps = pa.getPredicate();
			Term[] args = recReplace(engine,pa.getParameters(),ps.getName().contains("="),nomap);
			return args == null ? Atom.TRUE : engine.getSMTTheory().atom(ps,args);
		} else if( f instanceof QuantifiedFormula ) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			int quantifier = qf.getQuantifier();
			SMTLibBase[][] triggers = qf.getTriggers();
			TermVariable[] termvars = qf.getVariables();
			Formula rsub = recReplace(engine,qf.getSubformula(),nomap);
			return quantifier == QuantifiedFormula.EXISTS ? engine.getSMTTheory().exists(termvars,rsub)
					: engine.getSMTTheory().forall(termvars,rsub,triggers);
		} else if( f instanceof ITEFormula ) {
			ITEFormula ite = (ITEFormula)f;
			Formula prem = recReplace(engine,ite.getCondition(),nomap);
			Formula thenf = recReplace(engine,ite.getTrueCase(),nomap);
			Formula elsef = recReplace(engine,ite.getFalseCase(),nomap);
			return engine.getSMTTheory().ifthenelse(prem,thenf,elsef);
		} else if( f instanceof Atom ) {
			return f;
		}
		throw new IllegalArgumentException("Formula Type is not implemented yet since it should not occur in an interpolant: " + f.getClass().getName());
	}
	
	public static InterpolationInfo simpAndReplace(DPLLEngine engine,Formula f,HashMap<DPLLAtom,Interpolator> mixed,NOEqMap nomap) {
//		System.err.println("Substitute: Input Formula is " + f);
//		System.err.println("Applying subsitution map: " + nomap);
		Formula res = recReplace(engine,f,nomap);
//		System.err.println("Substitute: Output Formula is " + res);
		InterpolationInfo info = new InterpolationInfo(res,mixed);
		return info;
	}

}
