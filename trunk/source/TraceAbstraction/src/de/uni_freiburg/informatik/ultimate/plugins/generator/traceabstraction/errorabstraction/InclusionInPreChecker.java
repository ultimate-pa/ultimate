/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * Checks the implication (the name 'Hoare triple checker' is misleading) {@literal P => ¬ wp(¬ P', st)} which is
 * equivalent to {@literal P => pre(P', st)}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class InclusionInPreChecker implements IHoareTripleChecker {
	// apply nontrivial quantifier elimination
	private static final boolean EXPENSIVE_PQE_FOR_WP_RESULTS = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final MonolithicImplicationChecker mMic;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPt;
	private final PredicateFactory mPf;
	private final CfgSmtToolkit mCsToolkit;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param logger
	 *            logger
	 * @param mic
	 *            monolithic implication checker
	 * @param predicateTransformer
	 *            predicate transfomer
	 * @param predicateFactory
	 *            predicate factory
	 * @param csToolkit
	 *            SMT toolkit
	 */
	public InclusionInPreChecker(final IUltimateServiceProvider services, final ILogger logger,
			final MonolithicImplicationChecker mic,
			final PredicateTransformer<Term, IPredicate, TransFormula> predicateTransformer,
			final PredicateFactory predicateFactory, final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = logger;
		mMic = mic;
		mPt = predicateTransformer;
		mPf = predicateFactory;
		mCsToolkit = csToolkit;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpInternal(act, succ)));
		final Validity result = checkImplication(pre, preFormula);
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpCall(act, succ)));
		final Validity result = checkImplication(pre, preFormula);
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		final IPredicate preFormula = mPf.not(mPf.newPredicate(getWpReturn(preHier, act, succ)));
		final Validity result = checkImplication(preLin, preFormula);
		return result;
	}

	@Override
	public void releaseLock() {
		// TODO 2017-05-17 Christian: What to do here?
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		// TODO 2017-05-17 Christian: What to do here?
		return null;
	}

	private Validity checkImplication(final IPredicate pre, final IPredicate succ) {
		return mMic.checkImplication(pre, false, succ, false);
	}

	private Term getWpInternal(final IInternalAction act, final IPredicate succ) {
		Term result = mPt.weakestPrecondition(mPf.not(succ), act.getTransformula());
		if (EXPENSIVE_PQE_FOR_WP_RESULTS) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mCsToolkit.getManagedScript(),
					result, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		}
		return result;
	}

	private Term getWpCall(final ICallAction act, final IPredicate succ) {
		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(act.getSucceedingProcedure());
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(act.getSucceedingProcedure());
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(act.getSucceedingProcedure());
		Term result = mPt.weakestPreconditionCall(mPf.not(succ), act.getTransformula(), globalVarsAssignments,
				oldVarAssignments, modifiableGlobals);
		if (EXPENSIVE_PQE_FOR_WP_RESULTS) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mCsToolkit.getManagedScript(),
					result, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		}
		return result;
	}

	// TODO 2017-06-09 Christian: Do we need to change preHier to 'true'? See USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP.
	private Term getWpReturn(final IPredicate preHier, final IReturnAction act, final IPredicate succ) {
		final TransFormula returnTf = act.getAssignmentOfReturn();
		final TransFormula callTf = act.getLocalVarsAssignmentOfCall();
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(act.getSucceedingProcedure());
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(act.getSucceedingProcedure());
		Term result = mPt.weakestPreconditionReturn(mPf.not(succ), preHier, returnTf, callTf, oldVarAssignments,
				modifiableGlobals);
		if (EXPENSIVE_PQE_FOR_WP_RESULTS) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mCsToolkit.getManagedScript(),
					result, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		}
		return result;
	}
}
