/*
 * Copyright (C) 2009-2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * The SymbolCollector collects all function symbols occuring in a term. This non-recursively walks over a term and its
 * subterms and for each application term it collects the function symbol unless it is internal. The collector can be
 * used with more than one formula. You can call {@link #collect} multiple times, then get the collected symbols of all
 * formulas with {@link #getSymbols}. Afterwards the collector is empty again and can be used to collect the symbols of
 * the next term.
 *
 * @author Christ, Hoenicke
 */
public class SymbolCollector extends NonRecursive {

	private HashSet<FunctionSymbol> mSymbols = new HashSet<FunctionSymbol>();
	private HashSet<Term> mVisited = new HashSet<Term>();

	/**
	 * Walk non-recursively over terms, and collect function symbols. Also walks through function definitions for
	 * defined functions.
	 *
	 * @author hoenicke
	 */
	public static class CollectWalker implements Walker {
		protected Term mTerm;
		public CollectWalker(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive walker) {
			final SymbolCollector collector = (SymbolCollector) walker;
			if (!collector.mVisited.add(mTerm)) {
				// we already visited this term.
				return;
			}
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
				final FunctionSymbol fsym = appTerm.getFunction();
				if (!fsym.isIntern()) {
					collector.mSymbols.add(appTerm.getFunction());
				}
				final Term definition = fsym.getDefinition();
				if (definition != null) {
					collector.enqueueWalker(new CollectWalker(definition));
				}
				final Term[] params = appTerm.getParameters();
				for (int i = 0; i < params.length; i++) {
					collector.enqueueWalker(new CollectWalker(params[i]));
				}
			} else if (mTerm instanceof LetTerm) {
				final LetTerm letTerm = (LetTerm) mTerm;
				final Term[] values = letTerm.getValues();
				for (int i = 0; i < values.length; i++) {
					collector.enqueueWalker(new CollectWalker(values[i]));
				}
				collector.enqueueWalker(new CollectWalker(letTerm.getSubTerm()));
			} else if (mTerm instanceof AnnotatedTerm) {
				collector.enqueueWalker(new CollectWalker(((AnnotatedTerm) mTerm).getSubterm()));
			} else if (mTerm instanceof QuantifiedFormula) {
				collector.enqueueWalker(new CollectWalker(((QuantifiedFormula) mTerm).getSubformula()));
			}
		}
	}


	/**
	 * Collect all symbols occurring in a given formula. This also collects the symbols used in defined functions.
	 *
	 * @param input
	 *            The given formula.
	 */
	public final void collect(final Term input) {
		run(new CollectWalker(input));
	}

	/**
	 * Returns the collected function symbols and clear the collector for the next task.
	 *
	 * @return the collected function symbols.
	 */
	public Set<FunctionSymbol> getSymbols() {
		final Set<FunctionSymbol> result = mSymbols;
		mSymbols = new HashSet<>();
		mVisited = new HashSet<>();
		return result;
	}
}
