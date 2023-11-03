/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.util.Collections;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.FixpointCheck.HasFixpoint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Additional fixpoint check also shows values. <br>
 * Work in progress. This is a workaround that encodes the loop in a predicate
 * and utilizes the {@link TraceCheck} for the stem. Hence this calls cannot yet
 * provide values for the loop. I think if we want to provide values for the loop
 * we have to extend the {@link TraceCheck}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class FixpointCheck2<L extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final NestedRun<L, IPredicate> mStem;
	private final TransFormula mLoop;
	private final HasFixpoint mResult;
	private InfiniteFixpointRepetitionWithExecution<L> mTerminationArgument;

	public FixpointCheck2(final IUltimateServiceProvider services, final ILogger logger, final CfgSmtToolkit csToolkit,
			final BasicPredicateFactory pf, final NestedRun<L, IPredicate> stem,
			final UnmodifiableTransFormula loopTF) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mStem = stem;
		mLoop = loopTF;

		// 20220926 Matthias: As precondition, we might need that global vars and
		// oldvars of the initial procedure coincide. But this seems to be a mistake
		// that we do in many places that that only is only problematic if the Boogie
		// program uses the `old` operator.
		final IPredicate precondition = pf.newPredicate(csToolkit.getManagedScript().getScript().term("true"));
		final IPredicate postcondition = constructNegatedLoopPredicate(services, csToolkit.getManagedScript(), pf,
				mLoop);
		final SortedMap<Integer, IPredicate> pendingContexts = Collections.emptySortedMap();
		final TraceCheck<L> tc = new TraceCheck<L>(precondition, postcondition, pendingContexts, mStem.getWord(),
				services, csToolkit, AssertCodeBlockOrder.NOT_INCREMENTALLY, true, false);
		switch (tc.isCorrect()) {
		case SAT:
			mResult = HasFixpoint.YES;
			if (!tc.providesRcfgProgramExecution()) {
				throw new AssertionError("TraceCheck has to provide an execution");
			}
			mTerminationArgument = new InfiniteFixpointRepetitionWithExecution<>(tc.getRcfgProgramExecution());
			break;
		case UNKNOWN:
			mResult = HasFixpoint.UNKNOWN;
			break;
		case UNSAT:
			mResult = HasFixpoint.NO;
			break;
		default:
			throw new AssertionError();
		}

	}

	private static IPredicate constructNegatedLoopPredicate(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory pf, final TransFormula loop) {
		final Term inVarsRenamed = TransFormulaUtils.renameInvarsToDefaultVars(loop, mgdScript, loop.getFormula());
		final Term allRenamed = TransFormulaUtils.renameOutvarsToDefaultVars(loop, mgdScript, inVarsRenamed);
		final Term withoutAuxVars = SmtUtils.quantifier(mgdScript.getScript(), QuantifiedFormula.EXISTS,
				loop.getAuxVars(), allRenamed);
		final Term elim = PartialQuantifierElimination.eliminate(services, mgdScript, withoutAuxVars,
				SimplificationTechnique.SIMPLIFY_DDA);
		return pf.newPredicate(SmtUtils.not(mgdScript.getScript(), elim));
	}

	public HasFixpoint getResult() {
		return mResult;
	}

	public InfiniteFixpointRepetitionWithExecution<L> getTerminationArgument() {
		return mTerminationArgument;
	}

}
