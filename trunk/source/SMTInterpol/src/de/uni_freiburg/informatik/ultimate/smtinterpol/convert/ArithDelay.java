/*
 * Copyright (C) 2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class ArithDelay extends InternTermTransformer {
	private final ScopedHashMap<Rational, Term> mArithConsts = 
			new ScopedHashMap<Rational, Term>();
	
	private Term replace(Rational constant, Theory t, Sort s) {
		Term replacement = mArithConsts.get(constant);
		if (replacement == null) {
			final String rep = "@" + constant.toString();
			FunctionSymbol fsym = t.getFunction(rep);
			if (fsym == null) {
				fsym = t.declareFunction(rep, Script.EMPTY_SORT_ARRAY, s);
			}
			replacement = t.term(fsym);
			mArithConsts.put(constant, replacement);
		}
		return replacement;
	}
	
	@Override
	public void convertApplicationTerm(
			ApplicationTerm appTerm, Term[] newArgs) {
		final Theory t = appTerm.getTheory();
		if (appTerm.getFunction().getName().equals("<=")) {
			final SMTAffineTerm arg0 = (SMTAffineTerm) newArgs[0];
			if (arg0.getConstant().compareTo(Rational.ZERO) != 0) {
				final Rational constant = arg0.getConstant();
				final Term replacement = replace(constant, t, arg0.getSort());
				final Map<Term, Rational> summands =
						new HashMap<Term, Rational>(arg0.getSummands());
				summands.put(replacement, Rational.ONE);
				final SMTAffineTerm res = SMTAffineTerm.create(
						summands, Rational.ZERO, arg0.getSort());
				setResult(t.term(appTerm.getFunction(), res, newArgs[1]));
				return;
			}
		} else if (appTerm.getFunction().getName().equals("=")) {
			Term[] args = newArgs;
			for (int i = 0; i < newArgs.length; ++i) {
				if (args[i] instanceof SMTAffineTerm) {
					final SMTAffineTerm arg = (SMTAffineTerm) args[i];
					if (arg.isConstant()) {
						if (newArgs == args) {
							args = newArgs.clone();
						}
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
					private final Iterator<Map.Entry<Rational, Term>> mIt =
							mArithConsts.entrySet().iterator();

					@Override
					public boolean hasNext() {
						return mIt.hasNext();
					}

					@Override
					public Term next() {
						final Map.Entry<Rational, Term> me = mIt.next();
						final Term val = me.getValue();
						final Theory t = val.getTheory();
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
		for (final Map.Entry<Rational, Term> me : mArithConsts.entrySet()) {
			final Term nkey = me.getValue();
			reverted.put(nkey, me.getKey().toTerm(nkey.getSort()));
		}
		return new InternTermTransformer() {

			@Override
			public void convertApplicationTerm(ApplicationTerm appTerm,
					Term[] newArgs) {
				final Term rep = reverted.get(appTerm);
				if (rep == null) {
					super.convertApplicationTerm(appTerm, newArgs);
				} else {
					setResult(rep);
				}
			}
		};
	}

	public boolean isEmpty() {
		return mArithConsts.isEmpty();
	}
	
	public void push() {
		mArithConsts.beginScope();
	}
	
	public void pop() {
		mArithConsts.endScope();
	}
	
}
