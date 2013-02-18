package local.stalin.logic;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

/**
 * This class removes flets and lets from formulae. Preserves structure of the
 * formula as much as possible.
 * @author Juergen Christ
 */
public class FormulaUnFleterer {
	private HashMap<FormulaVariable,Formula> fletmap = new HashMap<FormulaVariable, Formula>();
	private HashMap<TermVariable,Term> letmap = new HashMap<TermVariable, Term>();
	private Theory t;
	private boolean isLazy;
	
	public FormulaUnFleterer(Theory theory) {
		this(theory, false);
	}
	/**
	 * Create a FormulaUnFleterer
	 * @param theory  the smt theory to use.
	 * @param lazy  true, if the right-hand-side of let/flet expression should only be expanded when
	 * the formula variable is expanded.  This contradicts the standard smtlib semantics but is needed
	 * for interpolation.
	 */
	public FormulaUnFleterer(Theory theory, boolean lazy) {
		t = theory;
		isLazy = lazy;
	}
	
	public void addSubstitutions(Map<FormulaVariable, Formula> formSubst, Map<TermVariable, Term> termSubst) {
		fletmap.putAll(formSubst);
		letmap.putAll(termSubst);
	}
	
	public Formula unflet(Formula f) {
		if (f instanceof NegatedFormula) {
			return t.not(unflet(((NegatedFormula) f).getSubFormula()));
		} else if (f instanceof FletFormula) {
			Stack<FormulaVariable> fletStack = new Stack<FormulaVariable>();
			while (f instanceof FletFormula) {
				FletFormula flet = (FletFormula) f;
				Formula flatform = isLazy ? flet.getValue() : unflet(flet.getValue());
				fletmap.put(flet.getVariable(), flatform);
				fletStack.push(flet.getVariable());
				f = flet.getSubFormula();
			}
			Formula result = unflet(f);
			while (!fletStack.isEmpty())
				fletmap.remove(fletStack.pop());
			return result;
		} else if (f instanceof LetFormula) {
			LetFormula let = (LetFormula) f;
			Term tvalue = isLazy ? let.getValue() : unlet(let.getValue());
			Term oldValue = letmap.put(let.getVariable(), tvalue);
			Formula result = unflet(let.getSubFormula());
			if (oldValue != null)
				letmap.put(let.getVariable(), oldValue);
			else
				letmap.remove(let.getVariable());
			return result;
		} else if (f instanceof ConnectedFormula) {
			Stack<Formula> parts = new Stack<Formula>();
			ConnectedFormula cf = (ConnectedFormula) f;
			int connector = cf.getConnector(); 
			Formula lhs = unflet(cf.getLhs());
			if (connector == ConnectedFormula.IFF
				|| connector == ConnectedFormula.XOR){
				/* Optimize repeated IFFs to prevent stack overflow. */
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula)cf.getRhs()).getConnector() == connector) {
					parts.push(lhs);
					cf = (ConnectedFormula) cf.getRhs();
					lhs = unflet(cf.getLhs());
				}
				// Small optimization: I do not push the last lhs
				Formula rhs = unflet(cf.getRhs());
				Formula res;
				if (connector == ConnectedFormula.XOR) {
					res = t.xor(lhs, rhs);
					while( !parts.isEmpty() )
						res = t.xor(parts.pop(), res);
				} else {
					res = t.iff(lhs, rhs);
					while( !parts.isEmpty() )
						res = t.iff(parts.pop(), res);
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
					lhs = unflet(cf.getLhs());
					if (lhs == Atom.TRUE)
						return Atom.TRUE;
					parts.add(lhs);
				}
				Formula result = unflet(cf.getRhs());
				while (!parts.isEmpty()) {
					result = t.or(parts.pop(), result);
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
					lhs = unflet(cf.getLhs());
					if (lhs == Atom.FALSE)
						return Atom.FALSE;
					parts.add(lhs);
				}
				Formula result = unflet(cf.getRhs());
				while (!parts.isEmpty()) {
					result = t.and(parts.pop(), result);
				}
				return result;
			} else {
				assert(connector == ConnectedFormula.IMPLIES);
				return t.implies(lhs,unflet(cf.getRhs()));
			}
		} else if (f instanceof ITEFormula) {
			ITEFormula ite = (ITEFormula) f;
			return t.ifthenelse(unflet(ite.getCondition()),unflet(ite.getTrueCase()),unflet(ite.getFalseCase()));
		} else if (f instanceof VariableAtom) {
			FormulaVariable fv = ((VariableAtom)f).getVariable();
			if (fletmap.containsKey(fv)) {
				f = fletmap.get(fv);
				if (isLazy)
					f = unflet(f);
			}
			return f;
		} else if (f instanceof DistinctAtom) {
			Term[] terms = ((DistinctAtom)f).getTerms();
			Term[] newterms = new Term[terms.length];
			for( int i = 0; i < terms.length; ++i )
				newterms[i] = unlet(terms[i]);
			return t.distinct(newterms);
		} else if (f instanceof EqualsAtom) {
			Term[] terms = ((EqualsAtom)f).getTerms();
			Term[] newterms = new Term[terms.length];
			for( int i = 0; i < terms.length; ++i )
				newterms[i] = unlet(terms[i]);
			return t.equals(newterms);
		} else if (f instanceof PredicateAtom) {
			PredicateAtom pa = (PredicateAtom)f;
			Term[] args = pa.getParameters();
			Term[] newargs = new Term[args.length];
			for( int i = 0; i < args.length; ++i )
				newargs[i] = unlet(args[i]);
			return t.atom(pa.getPredicate(), newargs);
		} else if (f == Atom.FALSE) {
			return Atom.FALSE;
		} else if (f == Atom.TRUE) {
			return Atom.TRUE;
		} else if (f instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula)f;
			TermVariable[] vars = qf.getVariables();
			for( TermVariable tv : vars ) {
				Term old = letmap.put(tv,tv.createTerm());
				assert(old == null || old == tv.createTerm());
			}
			Formula sub = unflet(qf.getSubformula());
			SMTLibBase[][] triggers = qf.getTriggers();
			SMTLibBase[][] ntriggers = new SMTLibBase[triggers.length][];
			for (int i = 0; i < triggers.length; ++i) {
				SMTLibBase[] curtriggers = triggers[i];
				ntriggers[i] = new SMTLibBase[curtriggers.length];
				for (int j = 0; j < curtriggers.length; ++j) {
					if (curtriggers[j] instanceof Term)
						ntriggers[i][j] = unlet((Term)curtriggers[j]);
					else
						ntriggers[i][j] = unflet((Formula)curtriggers[j]);
				}
			}
			for( TermVariable tv : vars )
				letmap.remove(tv);
			return qf.getQuantifier() == QuantifiedFormula.EXISTS ? t.exists(vars,sub,ntriggers) : t.forall(vars,sub,ntriggers);
		} else {
			throw new IllegalArgumentException("Cannot handle formula "+f);
		}
	}
	public Term unlet(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm app = (ApplicationTerm)term;
			Term[] args = app.getParameters();
			Term[] newargs = new Term[args.length];
			boolean changed = false;
			for( int i = 0; i < args.length; ++i ) {
				newargs[i] = unlet(args[i]);
				if (newargs[i] != args[i])
					changed = true;
			}
			return changed ? t.term(app.getFunction(),newargs) : app;
		} else if (term instanceof ITETerm) {
			ITETerm ite = (ITETerm)term;
			return t.ite(unflet(ite.getCondition()),unlet(ite.getTrueCase()),unlet(ite.getFalseCase()));
		} else if (term instanceof VariableTerm) {
			TermVariable tv = ((VariableTerm)term).getVariable();
			Term term2 = term;
			if (letmap.containsKey(tv)) {
				term2 = letmap.get(tv);
				if (isLazy && term != term2)
					term2 = unlet(term2);
			}
			return term2;
		} else if (term instanceof NumeralTerm || term instanceof RationalTerm) {
			return term;
		} else {
			throw new IllegalArgumentException("Cannot handle: "+term);
		}
	}
}
