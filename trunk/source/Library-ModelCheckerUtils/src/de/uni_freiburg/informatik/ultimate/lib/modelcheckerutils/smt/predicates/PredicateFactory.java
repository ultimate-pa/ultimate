/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PredicateFactory extends BasicPredicateFactory {

	public PredicateFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable) {
		super(services, mgdScript, symbolTable);
	}

	public PredicateWithHistory newPredicateWithHistory(final IcfgLocation pp, final Term term,
			final Map<Integer, Term> history) {
		final TermVarsFuns tvp = constructTermVarsProc(term);
		final PredicateWithHistory pred = new PredicateWithHistory(pp, constructFreshSerialNumber(), tvp.getFormula(),
				tvp.getVars(), tvp.getFuns(), tvp.getClosedFormula(), history);
		return pred;
	}

	public SPredicate newSPredicate(final IcfgLocation pp, final Term term) {
		final TermVarsFuns termVarsProc = constructTermVarsProc(term);
		return newSPredicate(pp, termVarsProc);
	}

	SPredicate newSPredicate(final IcfgLocation pp, final TermVarsFuns termVarsProc) {
		final SPredicate pred = new SPredicate(pp, constructFreshSerialNumber(), termVarsProc.getFormula(),
				termVarsProc.getVars(), termVarsProc.getFuns(), termVarsProc.getClosedFormula());
		return pred;
	}

	public ISLPredicate newEmptyStackPredicate() {
		final IcfgLocation pp = new IcfgLocation(NoCallerDebugIdentifier.INSTANCE, "noCaller");
		return newSPredicate(pp,
				new TermVarsFuns(mEmptyStackTerm, EMPTY_VARS, Collections.emptySet(), mEmptyStackTerm));
	}

	public MLPredicate newMLPredicate(final IcfgLocation[] programPoints, final Term term) {
		final TermVarsFuns termVarsProc = constructTermVarsProc(term);
		final MLPredicate predicate =
				new MLPredicate(programPoints, constructFreshSerialNumber(), termVarsProc.getFormula(),
						termVarsProc.getVars(), termVarsProc.getFuns(), termVarsProc.getClosedFormula());
		return predicate;
	}

	public IPredicate newMLPredicate(final IcfgLocation[] programPoints, final ArrayList<Term> terms) {
		final IPredicate conjunction = andT(terms);
		return newMLPredicate(programPoints, conjunction.getFormula());
	}

	public MLPredicate newMLDontCarePredicate(final IcfgLocation[] programPoints) {
		return newMLPredicate(programPoints, mDontCareTerm);
	}

	private static final class NoCallerDebugIdentifier extends DebugIdentifier {

		public static final NoCallerDebugIdentifier INSTANCE = new NoCallerDebugIdentifier();

		private NoCallerDebugIdentifier() {
			// singleton constructor
		}

		@Override
		public String toString() {
			return "noCaller";
		}
	}

}
