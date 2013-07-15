package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class ArithDelay extends InternTermTransformer {
	private ScopedHashMap<Rational, Term> m_ArithConsts = 
			new ScopedHashMap<Rational, Term>();

	private final static Sort[] EMPTY_SORT_ARRAY = new Sort[0];
	
	private Term replace(Rational constant, Theory t, Sort s) {
		Term replacement = m_ArithConsts.get(constant);
		if (replacement == null) {
			String rep = "@" + constant.toString();
			FunctionSymbol fsym = t.getFunction(rep);
			if (fsym == null)
				fsym = t.declareFunction(rep, EMPTY_SORT_ARRAY, s);
			replacement = t.term(fsym);
			m_ArithConsts.put(constant, replacement);
		}
		return replacement;
	}
	
	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		Theory t = appTerm.getTheory();
		if (appTerm.getFunction().getName().equals("<=")) {
			SMTAffineTerm arg0 = (SMTAffineTerm) newArgs[0];
			if (arg0.getConstant().compareTo(Rational.ZERO) != 0) {
				Rational constant = arg0.getConstant();
				Term replacement = replace(constant, t, arg0.getSort());
				Map<Term, Rational> summands =
						new HashMap<Term, Rational>(arg0.getSummands());
				summands.put(replacement, Rational.ONE);
				SMTAffineTerm res = SMTAffineTerm.create(
						summands, Rational.ZERO, arg0.getSort());
				setResult(t.term(appTerm.getFunction(), res, newArgs[1]));
				return;
			}
		} else if (appTerm.getFunction().getName().equals("=")) {
			Term[] args = newArgs;
			for (int i = 0; i < newArgs.length; ++i) {
				if (args[i] instanceof SMTAffineTerm) {
					SMTAffineTerm arg = (SMTAffineTerm) args[i];
					if (arg.isConstant()) {
						if (newArgs == args)
							args = newArgs.clone();
						args[i] = replace(arg.getConstant(), t, arg.getSort());
					}
				}
			}
			setResult(t.term(appTerm.getFunction(), args));
			return;
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
	
	public Iterable<Term> getReplacedEqs() {
		return new Iterable<Term>() {
			
			@Override
			public Iterator<Term> iterator() {
				return new Iterator<Term>() {
					private Iterator<Map.Entry<Rational, Term>> m_It =
							m_ArithConsts.entrySet().iterator();

					@Override
					public boolean hasNext() {
						return m_It.hasNext();
					}

					@Override
					public Term next() {
						Map.Entry<Rational, Term> me = m_It.next();
						Term val = me.getValue();
						Theory t = val.getTheory();
						return t.term("=",
								me.getKey().toTerm(val.getSort()), val);
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
					
				};
			}
		};
	}
	
	public TermTransformer getReverter() {
		final HashMap<Term, Term> reverted = new HashMap<Term, Term>();
		for (Map.Entry<Rational, Term> me : m_ArithConsts.entrySet()) {
			Term nkey = me.getValue();
			reverted.put(nkey, me.getKey().toTerm(nkey.getSort()));
		}
		return new InternTermTransformer() {

			@Override
			public void convertApplicationTerm(ApplicationTerm appTerm,
					Term[] newArgs) {
				Term rep = reverted.get(appTerm);
				if (rep == null)
					super.convertApplicationTerm(appTerm, newArgs);
				else
					setResult(rep);
			}
		};
	}

	public boolean isEmpty() {
		return m_ArithConsts.isEmpty();
	}
	
	public void push() {
		m_ArithConsts.beginScope();
	}
	
	public void pop() {
		m_ArithConsts.endScope();
	}
	
}
