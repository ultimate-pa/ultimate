package local.stalin.logic;

import java.util.HashMap;
import java.util.Stack;

public class FormulaWalker {
	public interface SymbolVisitor {
		/**
		 * Returns the new term corresponding to <code>input</code>.
		 * @param input Input term.
		 * @return OutputTerm or <code>null</code> iff walker should descend into subterms (only for ApplicationTerms with arguments and ITETerms).
		 */
		public Term term(Term input);
		/**
		 * Finished descending into arguments of a term.
		 * @param input Term recently processed.
		 */
		public void done(Term input);
		/**
		 * Return a formula corresponding to this predicate atom.
		 * @param pa Predicate Atom just discovered in the formula.
		 * @return New formula or <code>pa</code> or <code>null</code> iff walker should descend into arguments.
		 */
		public Formula predicate(PredicateAtom pa);
		/**
		 * Finished descending into arguments of a predicate term.
		 * @param pa PredicateTerm recently processed.
		 */
		public void done(PredicateAtom pa);
		/**
		 * Whether flet formulae should be removed or not.
		 * @return <code>true</code> iff flets should be removed
		 */
		public boolean unflet();
		/**
		 * Should let formulae be removed or not. Note that the visitor is
		 * responsible for substituting TermVariables.
		 * @return <code>true</code> iff let formulae should be removed.
		 */
		public boolean unlet();
		/**
		 * Notification for a discovered let formula.
		 * @param tv   TermVariable bound by this let formula.
		 * @param mval Modified value of <code>tv</code>.
		 */
		public void let(TermVariable tv,Term mval);
		/**
		 * Begin of a quantifier scope.
		 * @param tvs Variables bound by this quantifier.
		 */
		public void quantifier(TermVariable[] tvs);
		/**
		 * End a scope of a variable.
		 * @param tv Variable whose scope ends.
		 */
		public void endscope(TermVariable tv);
		/**
		 * End scopes of multiple variables.
		 * @param tvs All variables whose scope ends.
		 */
		public void endscopes(TermVariable[] tvs);
	}
	private SymbolVisitor mvisitor;

	private Theory mtheory;
	private HashMap<FormulaVariable,Formula> mfletmap = null;
	public FormulaWalker(SymbolVisitor visitor,Theory theory) {
		mvisitor = visitor;
		mtheory = theory;
		if( mvisitor.unflet() )
			mfletmap = new HashMap<FormulaVariable,Formula>();
	}
	public Formula process(Formula in) {
		return recursivewalk(in);
	}
	private Formula recursivewalk(Formula in) {
		if (in instanceof NegatedFormula) {
			Formula sub = ((NegatedFormula)in).getSubFormula();
			Formula msub = recursivewalk(sub);
			return msub == sub ? in : mtheory.not(msub);
		} else if (in instanceof FletFormula) {
			FletFormula flet = (FletFormula)in;
			Formula mval = recursivewalk(flet.getValue());
			if( mvisitor.unflet() ) {
				mfletmap.put(flet.getVariable(),mval);
				try {
					return recursivewalk(flet.getSubFormula());
				} finally {
					mfletmap.remove(flet.getVariable());
				}
			}
			Formula msub = recursivewalk(flet.getSubFormula());
			return mval == flet.getValue() && msub == flet.getSubFormula() ? flet : mtheory.flet(flet.getVariable(),mval,msub);
		} else if (in instanceof LetFormula) {
			LetFormula let = (LetFormula) in;
			Term mval = walkterm(let.getValue());
			mvisitor.let(let.getVariable(),mval);
			try {
				Formula msub = recursivewalk(let.getSubFormula());
				return mvisitor.unlet() ? 
						msub : mval == let.getValue() && msub == let.getSubFormula() ? 
								let : 
									mtheory.let(let.getVariable(),mval,msub);
			} finally {
				mvisitor.endscope(let.getVariable());
			}
		} else if (in instanceof ConnectedFormula) {
			Stack<Formula> parts = new Stack<Formula>();
			ConnectedFormula cf = (ConnectedFormula)in;
			int connector = cf.getConnector(); 
			Formula lhs = recursivewalk(cf.getLhs());
			if (connector == ConnectedFormula.IFF
				|| connector == ConnectedFormula.XOR){
				/* Optimize repeated IFFs to prevent stack overflow. */
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					parts.push(lhs);
					cf = (ConnectedFormula) cf.getRhs();
					lhs = recursivewalk(cf.getLhs());
				}
				// Small optimization: I do not push the last lhs
				Formula rhs = recursivewalk(cf.getRhs());
				Formula res;
				if (connector == ConnectedFormula.XOR) {
					res = mtheory.xor(lhs, rhs);
					while( !parts.isEmpty() )
						res = mtheory.xor(parts.pop(), res);
				} else {
					res = mtheory.iff(lhs, rhs);
					while( !parts.isEmpty() )
						res = mtheory.iff(parts.pop(), res);
				}
				return res;
			} else if (connector == ConnectedFormula.OR) {
				/* Optimize repeated disjunctions to prevent stack overflow. */
				if (lhs == Atom.TRUE)
					return Atom.TRUE;
				parts.add(lhs);
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					cf = (ConnectedFormula) cf.getRhs();
					lhs = recursivewalk(cf.getLhs());
					if (lhs == Atom.TRUE)
						return Atom.TRUE;
					parts.add(lhs);
				}
				Formula result = recursivewalk(cf.getRhs());
				while (!parts.isEmpty()) {
					result = mtheory.or(parts.pop(), result);
				}
				return result;
			} else if (connector == ConnectedFormula.AND) {
				/* Optimize repeated conjunctions to prevent stack overflow. */
				if (lhs == Atom.FALSE)
					return Atom.FALSE;
				parts.add(lhs);
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					cf = (ConnectedFormula) cf.getRhs();
					lhs = recursivewalk(cf.getLhs());
					if (lhs == Atom.FALSE)
						return Atom.FALSE;
					parts.add(lhs);
				}
				Formula result = recursivewalk(cf.getRhs());
				while (!parts.isEmpty()) {
					result = mtheory.and(parts.pop(),result);
				}
				return result;
			} else if (connector == ConnectedFormula.IMPLIES) {
				return mtheory.implies(lhs,recursivewalk(cf.getRhs()));
			} else if (connector == ConnectedFormula.OEQ) {
				return mtheory.oeq(lhs, recursivewalk(cf.getRhs()));
			} else {
				throw new InternalError("Unimplmented formula type!!!");
			}
		} else if (in instanceof ITEFormula) {
			ITEFormula ite = (ITEFormula)in;
			Formula mcond = recursivewalk(ite.getCondition());
			Formula mtc = recursivewalk(ite.getTrueCase());
			Formula mfc = recursivewalk(ite.getFalseCase());
			return mcond == ite.getCondition() && mtc == ite.getTrueCase() && mfc == ite.getFalseCase() ? 
					ite : mtheory.ifthenelse(mcond,mtc,mfc);
		} else if (in instanceof VariableAtom) {
			if( mvisitor.unflet() ) {
				Formula res = mfletmap.get(((VariableAtom)in).getVariable());
				if( res == null ) throw new IllegalArgumentException("Malformed formula: unbound formula variable!");
				return res;
			}
			return in;
		} else if (in instanceof DistinctAtom) {
			Term[] terms = ((DistinctAtom)in).getTerms();
			Term[] newterms = new Term[terms.length];
			boolean changed = false;
			for( int i = 0; i < terms.length; ++i ) {
				changed |= (newterms[i] = walkterm(terms[i])) != terms[i];
			}
			return changed ? mtheory.distinct(newterms) : in;
		} else if (in instanceof EqualsAtom) {
			Term[] terms = ((EqualsAtom)in).getTerms();
			Term[] newterms = new Term[terms.length];
			boolean changed = false;
			for( int i = 0; i < terms.length; ++i )
				changed |= (newterms[i] = walkterm(terms[i])) != terms[i];
			return changed ? mtheory.equals(newterms) : in;
		} else if (in instanceof PredicateAtom) {
			PredicateAtom pa = (PredicateAtom)in;
			Formula res = mvisitor.predicate(pa);
			if( res != null )
				return res;
			Term[] args = pa.getParameters();
			Term[] nargs = new Term[args.length];
			boolean changed = false;
			for( int i = 0; i < args.length; ++i )
				changed |= (nargs[i] = walkterm(args[i])) != args[i];
			mvisitor.done(pa);
			return changed ? mtheory.atom(pa.getPredicate(),nargs) : in;
		} else if (in == Atom.FALSE) {
			return Atom.FALSE;
		} else if (in == Atom.TRUE) {
			return Atom.TRUE;
		} else if (in instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula)in;
			TermVariable[] vars = qf.getVariables();
			mvisitor.quantifier(vars);
			try {
				Formula msub = recursivewalk(qf.getSubformula());
				SMTLibBase[][] triggers = qf.getTriggers();
				SMTLibBase[][] ntrigs = new SMTLibBase[triggers.length][];
				boolean changed = msub != qf.getSubformula();
				for (int i = 0; i < triggers.length; ++i) {
					ntrigs[i] = new SMTLibBase[triggers[i].length];
					for (int j = 0; j < triggers[i].length; ++j) {
						SMTLibBase oldTrigger = triggers[i][j];
						changed |= 
							(ntrigs[i][j] = oldTrigger instanceof Term ? walkterm((Term)oldTrigger) : recursivewalk((Formula)oldTrigger)) != oldTrigger;
					}
				}
				return changed ? 
						qf.getQuantifier() == QuantifiedFormula.EXISTS ? 
								mtheory.exists(vars,msub,ntrigs) : 
									mtheory.forall(vars,msub,ntrigs) :
										qf;
			} finally {
				mvisitor.endscopes(vars);
			}
		} else {
			throw new IllegalArgumentException("Cannot handle formula "+in);
		}
	}
	private Term walkterm(Term t) {
		Term res = mvisitor.term(t);
		if( res != null )
			return res;
		if( t instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)t;
			Term[] args = at.getParameters();
			Term[] nargs = new Term[args.length];
			boolean changed = false;
			for( int i = 0; i < args.length; ++i )
				changed |= (nargs[i] = walkterm(args[i])) != args[i];
			mvisitor.done(t);
			return changed ? mtheory.term(at.getFunction(),nargs) : t;
		} else if( t instanceof ITETerm ) {
			ITETerm itet = (ITETerm)t;
			Formula mcond = recursivewalk(itet.getCondition());
			Term tc = walkterm(itet.getTrueCase());
			Term fc = walkterm(itet.getFalseCase());
			mvisitor.done(t);
			return mcond == itet.getCondition() && tc == itet.getTrueCase() && fc == itet.getFalseCase() ? t : mtheory.ite(mcond,tc,fc);
		}
		throw new RuntimeException("SymbolVisitor returned null-value for basic term!");
	}
}
