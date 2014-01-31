/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * A walker according to the visitor pattern.  This walker is recursive.  Since
 * this is dangerous for big terms, it should not be used anymore.  Consider
 * {@link NonRecursive} or {@link TermTransformer} instead.
 * @author Juergen Christ
 */
@Deprecated
public class FormulaWalker {
	public interface SymbolVisitor {
		/**
		 * Returns the new term corresponding to <code>input</code>.
		 * @param input Input term.
		 * @return OutputTerm or <code>null</code> iff walker should descend
		 *         into subterms (only for ApplicationTerms with arguments and
		 *         ITETerms).
		 */
		public Term term(Term input);
		/**
		 * Finished descending into arguments of a term.
		 * @param input Term recently processed.
		 */
		public void done(Term input);
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
		public void let(TermVariable[] tv,Term[] mval);
		/**
		 * Begin of a quantifier scope.
		 * @param tvs Variables bound by this quantifier.
		 */
		public void quantifier(TermVariable[] tvs);
		/**
		 * End scopes of multiple variables.
		 * @param tv All variables whose scope ends.
		 */
		public void endscope(TermVariable[] tv);
	}
	private final SymbolVisitor mVisitor;

	private final Script mScript;
	public FormulaWalker(SymbolVisitor visitor, Script script) {
		mVisitor = visitor;
		mScript = script;
	}

	public Term process(Term term) throws SMTLIBException {
		return recursivewalk(term);
	}
	private Term recursivewalk(Term term) throws SMTLIBException {
		Term res = mVisitor.term(term);
		if (res != null)
			return res;
		if (term instanceof LetTerm) {
			LetTerm let = (LetTerm) term;
			Term[] values = let.getValues();
			Term[] newvalues = new Term[values.length];
			boolean changed = false;
			for (int i = 0; i < values.length; i++) {
				newvalues[i] = recursivewalk(values[i]);
				if (newvalues[i] != values[i])
					changed = true;
			}
			if (!changed)
				newvalues = values;
			mVisitor.let(let.getVariables(), newvalues);
			try {
				Term newsub = recursivewalk(let.getSubTerm());
				return mVisitor.unlet() ? newsub
					: newvalues == values && newsub == let.getSubTerm() ? let 
						: mScript.let(let.getVariables(), newvalues, newsub);
			} finally {
				mVisitor.endscope(let.getVariables());
			}
		} else if (term instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula)term;
			int quantifier = qf.getQuantifier();
			TermVariable[] vars = qf.getVariables();
			mVisitor.quantifier(vars);
			try {
				Term msub = recursivewalk(qf.getSubformula());
				boolean changed = msub != qf.getSubformula();
				return changed ? qf : mScript.quantifier(
						quantifier, vars, msub);

			} finally {
				mVisitor.endscope(vars);
			}
		} else if (term instanceof AnnotatedTerm) {
			AnnotatedTerm annterm = (AnnotatedTerm) term;
			Term sub = recursivewalk(annterm.getSubterm());
			Annotation[] annots = annterm.getAnnotations();
			Annotation[] newAnnots = annots;
			for (int i = 0; i < annots.length; i++) {
				Object value = annots[i].getValue();
				Object newValue;
				if (value instanceof Term)
					newValue = recursivewalk((Term) value);
				else if (value instanceof Term[])
					newValue = recursivewalk((Term[]) value);
				else
					newValue = value;
				if (newValue != value) {
					if (annots == newAnnots)
						newAnnots = annots.clone();
					newAnnots[i] = new Annotation(annots[i].getKey(), newValue);
				}
			}
			if (sub == annterm.getSubterm()	&& newAnnots == annots)
				return term;
			return mScript.annotate(sub, newAnnots);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) term;
			Term[] args = at.getParameters();
			Term[] nargs = recursivewalk(args);
			mVisitor.done(term);
			return args == nargs ? term : mScript.term(
					at.getFunction().getName(),nargs);
		}
		throw new RuntimeException(
				"SymbolVisitor returned null-value for basic term!");
	}

	private Term[] recursivewalk(Term[] args) throws SMTLIBException {
		Term[] nargs = new Term[args.length];
		boolean changed = false;
		for (int i = 0; i < args.length; ++i) {
			nargs[i] = recursivewalk(args[i]);
			if (nargs[i] != args[i])
				changed = true;
		}
		return changed ? nargs : args;
	}
}
