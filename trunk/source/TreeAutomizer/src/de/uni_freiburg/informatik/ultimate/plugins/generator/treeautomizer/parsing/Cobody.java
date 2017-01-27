/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class Cobody {
	Set<Term> transitions;
	Set<ApplicationTerm> predicates;
	Map<HCVar, TermVariable> inVars;

	public Cobody() {
		predicates = new HashSet<>();
		transitions = new HashSet<>();
		inVars = new HashMap<>();
	}

	public void addPredicate(ApplicationTerm literal) {
		predicates.add(literal);
	}

	public void addTransitionFormula(Term formula) {
		transitions.add(formula);
	}

	public void mergeCobody(Cobody cobody) {
		for (final ApplicationTerm predicate : cobody.predicates) {
			addPredicate(predicate);
		}
		for (final Term transition : cobody.transitions) {
			addTransitionFormula(transition);
		}
	}
	
	public Body negate() {
		final Body res = new Body();
		res.mergeCobody(this);
		return res;
	}

	public Term getTransitionFormula(ManagedScript script) {
		return Util.and(script.getScript(), transitions.toArray(new Term[transitions.size()]));
	}

	public Map<HornClausePredicateSymbol, List<TermVariable>> getPredicateToVars(
			final HCSymbolTable symbolTable) {

		final HashMap<HornClausePredicateSymbol, List<TermVariable>> res = new HashMap<>();
		for (final ApplicationTerm predicate : predicates) {
			final ArrayList<TermVariable> vars = new ArrayList<>();
			for (final Term par : predicate.getParameters()) {
				vars.add((TermVariable) par);
			}

			res.put(symbolTable.getOrConstructHornClausePredicateSymbol(
						predicate.getFunction().getName(), predicate.getFunction().getParameterSorts()), 
					vars);
		}
		return res;
	}

	@Override
	public String toString() {
		String res = "";
		boolean first = true;
		for (final ApplicationTerm t : predicates) {
			if (!first) {
				res += " && ";
			}
			res += t.toString();
			first = false;
		}
		for (final Term t : transitions) {
			if (!first) {
				res += " && ";
			}
			res += t.toStringDirect();
			first = false;
		}
		return '(' + res + ')';
	}
}
