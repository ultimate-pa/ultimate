/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermVarsProc {
	private final Term mTerm;
	private final Set<IProgramVar> mVars;
	private final String[] mProcedures;
	private final Term mClosedTerm;

	public TermVarsProc(final Term term, final Set<IProgramVar> vars, final String[] procedures,
			final Term closedTerm) {
		mTerm = term;
		mVars = vars;
		mProcedures = procedures;
		mClosedTerm = closedTerm;
	}

	public String[] getProcedures() {
		return mProcedures;
	}

	public Term getFormula() {
		return mTerm;
	}

	public Term getClosedFormula() {
		return mClosedTerm;
	}

	public Set<IProgramVar> getVars() {
		return mVars;
	}

	/**
	 * Given a term in which every free variable is the TermVariable of a BoogieVar. Compute the BoogieVars of the free
	 * variables and the procedures of these BoogieVariables.
	 */
	public static TermVarsProc computeTermVarsProc(final Term term, final Script script,
			final IIcfgSymbolTable symbolTable) {
		return computeTermVarsProc(term, script, symbolTable::getProgramVar);
	}

	/**
	 * Given a term in which every free variable is the TermVariable of a BoogieVar. Compute the BoogieVars of the free
	 * variables and the procedures of these BoogieVariables.
	 */
	public static TermVarsProc computeTermVarsProc(final Term term, final Script script,
			final Function<TermVariable, IProgramVar> funTermVar2ProgVar) {
		final HashSet<IProgramVar> vars = new HashSet<>();
		final Set<String> procs = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = funTermVar2ProgVar.apply(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding IProgramVar for " + tv);
			}
			vars.add(bv);
			if (bv.getProcedure() != null) {
				procs.add(bv.getProcedure());
			}
		}
		final Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, script);
		return new TermVarsProc(term, vars, procs.toArray(new String[procs.size()]), closedTerm);
	}

	/**
	 * Given a term in which every free variable is the TermVariable of a BoogieVar. Compute the BoogieVars of the free
	 * variables and the procedures of these BoogieVariables. If replaceNonModifiableOldVars is true, modifiableGlobals
	 * must be non-null and we check we replace the oldVars of all non-modifiable Globals by their corresponding
	 * non-oldVars.
	 *
	 * 2015-05-27 Matthias: At the moment, I don't know if we need this method. Don't use it unless you know what you
	 * do.
	 */
	@Deprecated
	private static TermVarsProc computeTermVarsProc(Term term, final Boogie2SMT boogie2smt,
			final boolean replaceNonModifiableOldVars, final Set<IProgramVar> modifiableGlobals) {
		final HashSet<IProgramVar> vars = new HashSet<>();
		final List<IProgramOldVar> oldVarsThatHaveToBeReplaced = new ArrayList<>();
		final Set<String> procs = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			IProgramVar bv = boogie2smt.getBoogie2SmtSymbolTable().getProgramVar(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding IProgramVar for " + tv);
			}
			if (replaceNonModifiableOldVars) {
				if (bv instanceof IProgramOldVar) {
					final IProgramNonOldVar nonOld = ((IProgramOldVar) bv).getNonOldVar();
					if (modifiableGlobals.contains(nonOld)) {
						// do nothing - is modifiable
					} else {
						oldVarsThatHaveToBeReplaced.add((IProgramOldVar) bv);
						bv = nonOld;
					}
				}
			}
			vars.add(bv);
			if (bv.getProcedure() != null) {
				procs.add(bv.getProcedure());
			}
		}
		if (!oldVarsThatHaveToBeReplaced.isEmpty()) {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final IProgramOldVar oldVar : oldVarsThatHaveToBeReplaced) {
				final IProgramNonOldVar nonOld = oldVar.getNonOldVar();
				substitutionMapping.put(oldVar.getTermVariable(), nonOld.getTermVariable());
			}
			term = new Substitution(boogie2smt.getScript(), substitutionMapping).transform(term);
		}
		final Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, boogie2smt.getScript());
		return new TermVarsProc(term, vars, procs.toArray(new String[procs.size()]), closedTerm);
	}

}
