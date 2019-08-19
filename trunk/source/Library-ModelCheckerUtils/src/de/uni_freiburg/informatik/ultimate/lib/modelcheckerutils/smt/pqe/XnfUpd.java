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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NonTheorySymbol.Variable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class XnfUpd extends XjunctPartialQuantifierElimination {

	public XnfUpd(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "unconnected parameter drop";
	}

	@Override
	public String getAcronym() {
		return "UPD";
	}

	@Override
	public boolean resultIsXjunction() {
		return true;
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] dualJuncts, final Set<TermVariable> eliminatees) {
		final Set<TermVariable> occuringVars = new HashSet<>();
		for (final Term param : dualJuncts) {
			occuringVars.addAll(Arrays.asList(param.getFreeVars()));
		}

		eliminatees.retainAll(occuringVars);

		final ConnectionPartition connection = new ConnectionPartition(Arrays.asList(dualJuncts));
		final List<TermVariable> removeableTvs = new ArrayList<>();
		final List<TermVariable> unremoveableTvs = new ArrayList<>();
		final List<Term> removeableTerms = new ArrayList<>();
		final List<Term> unremoveableTerms = new ArrayList<>();
		for (final Set<NonTheorySymbol<?>> connectedSymbols : connection.getConnectedNonTheorySymbols()) {
			final Set<Term> connectedTerms = connection.getTermsOfConnectedNonTheorySymbols(connectedSymbols);
			final Set<TermVariable> freeVarsOfConnectedTerms = SmtUtils.getFreeVars(connectedTerms);
			final boolean isSuperfluous;
			if (!containsOnlyVariables(connectedSymbols)) {
				isSuperfluous = false;
			} else {
				if (quantifier == QuantifiedFormula.EXISTS) {
					final Term simplified =
							isSuperfluousConjunction(mScript, connectedTerms, freeVarsOfConnectedTerms, eliminatees);
					if (SmtUtils.isTrueLiteral(simplified)) {
						isSuperfluous = true;
					} else if (SmtUtils.isFalseLiteral(simplified)) {
						return new Term[] { simplified };
					} else if (simplified == null) {
						isSuperfluous = false;
					} else {
						throw new AssertionError("illegal case");
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					final Term simplified =
							isSuperfluousDisjunction(mScript, connectedTerms, freeVarsOfConnectedTerms, eliminatees);
					if (SmtUtils.isFalseLiteral(simplified)) {
						isSuperfluous = true;
					} else if (SmtUtils.isTrueLiteral(simplified)) {
						return new Term[] { simplified };
					} else if (simplified == null) {
						isSuperfluous = false;
					} else {
						throw new AssertionError("illegal case");
					}
				} else {
					throw new AssertionError("unknown quantifier");
				}
			}
			if (isSuperfluous) {
				removeableTvs.addAll(freeVarsOfConnectedTerms);
				removeableTerms.addAll(connectedTerms);
			} else {
				unremoveableTvs.addAll(freeVarsOfConnectedTerms);
				unremoveableTerms.addAll(connectedTerms);
			}
		}
		final List<Term> termsWithoutTvs = connection.getTermsWithNonTheorySymbols();
		assert occuringVars.size() == removeableTvs.size() + unremoveableTvs.size();
		assert dualJuncts.length == removeableTerms.size() + unremoveableTerms.size() + termsWithoutTvs.size();
		for (final Term termWithoutTvs : termsWithoutTvs) {
			final LBool sat = Util.checkSat(mScript, termWithoutTvs);
			if (sat == LBool.UNSAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					eliminatees.clear();
					return new Term[] { mScript.term("false") };
				} else if (quantifier == QuantifiedFormula.FORALL) {
					// we drop this term its equivalent to false
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else if (sat == LBool.SAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					// we drop this term its equivalent to true
				} else if (quantifier == QuantifiedFormula.FORALL) {
					eliminatees.clear();
					return new Term[] { mScript.term("true") };
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				throw new AssertionError("expecting sat or unsat");
			}
		}
		if (removeableTerms.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new DebugMessage("not eliminated quantifier via UPD for {0}", occuringVars));
			}
			return dualJuncts;
		}
		eliminatees.removeAll(removeableTvs);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(new DebugMessage("eliminated quantifier via UPD for {0}", removeableTvs));
		}
		final Term[] result;
		if (unremoveableTerms.isEmpty()) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				result = new Term[] { mScript.term("true") };
			} else if (quantifier == QuantifiedFormula.FORALL) {
				result = new Term[] { mScript.term("false") };
			} else {
				throw new AssertionError("unknown quantifier");
			}
		} else {
			result = unremoveableTerms.toArray(new Term[unremoveableTerms.size()]);
		}
		return result;

	}

	private static boolean containsOnlyVariables(final Set<NonTheorySymbol<?>> connectedSymbols) {
		final Predicate<? super NonTheorySymbol<?>> predicate = x -> (x instanceof Variable);
		return connectedSymbols.stream().allMatch(predicate);
	}

	/**
	 * Return "true" if connectedVars is a subset of quantifiedVars and the conjunction of terms is satisfiable. Return
	 * "false" if connectedVars is a subset of quantifiedVars and the conjunction of terms is not satisfiable. Return
	 * null otherwise
	 */
	public static Term isSuperfluousConjunction(final Script script, final Set<Term> terms,
			final Set<TermVariable> connectedVars, final Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {

			final Term conjunction = SmtUtils.and(script, terms);
			final LBool isSat = Util.checkSat(script, conjunction);
			if (isSat == LBool.SAT) {
				return script.term("true");
			} else if (isSat == LBool.UNSAT) {
				return script.term("false");
			}
		}
		return null;
	}

	/**
	 * Return "false" if connectedVars is a subset of quantifiedVars and the conjunction of terms is not valid. Return
	 * "true" if connectedVars is a subset of quantifiedVars and the conjunction of terms is valid. Return null
	 * otherwise
	 */
	public static Term isSuperfluousDisjunction(final Script script, final Set<Term> terms,
			final Set<TermVariable> connectedVars, final Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			final Term disjunction = SmtUtils.or(script, terms.toArray(new Term[terms.size()]));
			final LBool isSat = Util.checkSat(script, SmtUtils.not(script, disjunction));
			if (isSat == LBool.SAT) {
				return script.term("false");
			} else if (isSat == LBool.UNSAT) {
				return script.term("true");
			}
		}
		return null;
	}

}
