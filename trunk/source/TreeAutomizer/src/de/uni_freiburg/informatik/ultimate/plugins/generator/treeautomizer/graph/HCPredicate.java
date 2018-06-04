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
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * A predicate object for HornClauses.
 * 
 * Convention: The "signature" of any Predicate that we use in TreeAutomizer is fixed by a sequence of Sorts. (I.e. the
 * length and the contents of that sequence.) Thus the signature is given by a sequence of TermVariables. This sequence
 * is identical to the free variabels in the predicate's formula except for the ordering. Alternatively, the signature
 * can be given through an unordered set of TermVariables because we fix an (the natural?) ordering on the
 * TermVariables. (note sure about this..) Furthermore each of the free variables in the predicate formula corresponds
 * to an HCOutVar, which can also give us the "index" in the order of each of the free variables.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCPredicate extends BasicPredicate {
	private static final long serialVersionUID = 1750137515726690834L;
	private static final int SERIAL_HCPREDICATE = 1000000007;

	protected final Set<HcPredicateSymbol> mHcPredicateSymbols;

	private final List<TermVariable> mVariables;

	protected HCPredicate(final HcPredicateSymbol programPoint, final int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula, final List<TermVariable> variables) {
		this(programPoint, serialNumber, term, vars, closedFormula, variables, 0);
	}
	protected HCPredicate(final HcPredicateSymbol programPoint, final int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula, final List<TermVariable> variables, int dontCare) {
		super(serialNumber, new String[0], term, vars, closedFormula);
		mHcPredicateSymbols = Collections.singleton(programPoint);
		mVariables = variables;
	}

	protected HCPredicate(final HcPredicateSymbol programPoint, final Term term, final Set<IProgramVar> vars,
			final Term closedFormula, final List<TermVariable> variables) {
		this(programPoint, HashUtils.hashHsieh(SERIAL_HCPREDICATE, programPoint, term, variables), term, vars,
				closedFormula, variables);
	}


	protected HCPredicate(final Set<HcPredicateSymbol> programPoints, final int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula, final List<TermVariable> variables) {
		super(serialNumber, new String[0], term, vars, closedFormula);
		mHcPredicateSymbols = programPoints;
		mVariables = variables;
	}

	
	//here
	/*
	protected HCPredicate(final Set<HornClausePredicateSymbol> programPoints, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula, final List<TermVariable> variables) {
		this(programPoints, HashUtils.hashHsieh(SERIAL_HCPREDICATE, programPoints, term, variables), term, vars,
				closedFormula, variables);
	}
	*/

	@Override
	public String toString() {
		String result = "#";
		result += mHcPredicateSymbols;
		result += "@(" +  mFormula.toString() + ")";
		return result;
	}

	public Set<HcPredicateSymbol> getHcPredicateSymbols() {
		return mHcPredicateSymbols;
	}

	public List<TermVariable> getSignature() {
		return mVariables;
	}
	
}
