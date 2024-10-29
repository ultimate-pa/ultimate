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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class WorkerPredicateFactory extends PredicateFactory {

	public WorkerPredicateFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable) {
		super(services, mgdScript, symbolTable);
	}

	// @Override
	// public BasicPredicate newPredicate(Term term) {
	// // TODO This leads to the TermVarsProc Problem
	// // But without it, we get worker script predicates!!
	// System.out.println("NewPredicate: " + term);
	// System.out.println(term.getTheory());
	// final TermTransferrer tf = new TermTransferrer(mMgdScript.getScript(),
	// ((HistoryRecordingScript) mMgdScript.getScript()).getMainScript().getScript());
	// term = tf.transform(term);
	// System.out.println(term.getTheory());
	// System.out.println("End Predicate-----------------");
	// assert term == mDontCareTerm
	// || UltimateNormalFormUtils.respectsUltimateNormalForm(term) : "Term not in UltimateNormalForm";
	// final TermVarsProc termVarsProc = constructTermVarsProc(term);
	// final BasicPredicate predicate = new BasicPredicate(constructFreshSerialNumber(), termVarsProc.getProcedures(),
	// termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getFuns(),
	// termVarsProc.getClosedFormula());
	// return predicate;
	// }

}
