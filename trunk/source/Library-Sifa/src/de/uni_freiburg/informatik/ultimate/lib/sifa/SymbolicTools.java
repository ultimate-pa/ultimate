/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.Collection;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * Helper class to create and transform terms/formulas/predicates.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SymbolicTools {

	private final IIcfg<IcfgLocation> mIcfg;
	private final ManagedScript mMngdScript;
	private final PredicateFactory mFactory;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mTransformer;
	private final IPredicate mTop;
	private final IPredicate mBottom;
	private final SimplificationTechnique mSimplification;
	private final XnfConversionTechnique mXnfConversion;
	private final IUltimateServiceProvider mServices;
	private final ILogger mPQELogger;
	private final SifaStats mStats;

	public SymbolicTools(final IUltimateServiceProvider services, final SifaStats stats, final IIcfg<IcfgLocation> icfg,
			final SimplificationTechnique simplification, final XnfConversionTechnique xnfConversion) {
		mServices = services;
		mStats = stats;
		mIcfg = icfg;

		// create PQE logger with custom log level and silence ModelCheckerUtils logger
		mPQELogger = services.getLoggingService().getLogger(getClass().getName() + ".PQE");
		mPQELogger.setLevel(LogLevel.WARN);
		mServices.getLoggingService().setLogLevel(ModelCheckerUtils.PLUGIN_ID, LogLevel.WARN);

		mSimplification = simplification;
		mXnfConversion = xnfConversion;
		mMngdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final Script script = mMngdScript.getScript();
		mFactory = new PredicateFactory(services, mMngdScript, icfg.getCfgSmtToolkit().getSymbolTable());
		mTransformer = new PredicateTransformer<>(mMngdScript,
				new EliminatingTermDomainOperationProvider(services, mPQELogger, mMngdScript));
		mTop = mFactory.newPredicate(script.term("true"));
		mBottom = mFactory.newPredicate(script.term("false"));
	}

	public ManagedScript getManagedScript() {
		return mMngdScript;
	}

	public Script getScript() {
		return mMngdScript.getScript();
	}

	public PredicateFactory getFactory() {
		return mFactory;
	}

	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		mStats.start(SifaStats.Key.TOOLS_POST_TIME);
		mStats.increment(SifaStats.Key.TOOLS_POST_APPLICATIONS);
		final IPredicate postState =
				predicate(mTransformer.strongestPostcondition(input, transition.getTransformula()));
		mStats.stop(SifaStats.Key.TOOLS_POST_TIME);
		return postState;
	}

	/**
	 * Assigns arguments to parameters of the callee. Also handles globals and old vars.
	 */
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		mStats.start(SifaStats.Key.TOOLS_POST_CALL_TIME);
		mStats.increment(SifaStats.Key.TOOLS_POST_CALL_APPLICATIONS);
		final CfgSmtToolkit toolkit = mIcfg.getCfgSmtToolkit();
		final String calledProcedure = transition.getSucceedingProcedure();
		final Term postState = mTransformer.strongestPostconditionCall(input, transition.getLocalVarsAssignment(),
				toolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure),
				toolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure),
				toolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure));
		mStats.stop(SifaStats.Key.TOOLS_POST_CALL_TIME);
		return predicate(postState);
	}

	/**
	 * Assigns the return values from the callee to local variables of the caller. Also handles globals and old vars.
	 */
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		mStats.start(SifaStats.Key.TOOLS_POST_RETURN_TIME);
		mStats.increment(SifaStats.Key.TOOLS_POST_RETURN_APPLICATIONS);
		final CfgSmtToolkit toolkit = mIcfg.getCfgSmtToolkit();
		final String callee = returnTransition.getPrecedingProcedure();
		final IPredicate postState =
				predicate(mTransformer.strongestPostconditionReturn(inputBeforeReturn, inputBeforeCall,
						returnTransition.getTransformula(), returnTransition.getCorrespondingCall().getTransformula(),
						toolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee),
						toolkit.getModifiableGlobalsTable().getModifiedBoogieVars(callee)));
		mStats.stop(SifaStats.Key.TOOLS_POST_RETURN_TIME);
		return postState;
	}

	public Term[] dnfDisjuncts(final IPredicate pred) {
		// TODO consider using QuantifierPusher to push quantifiers as inward as possible

		// you can ensure that there are no let terms by using the unletter, but there should not be any let terms
		// final Term unletedTerm = new FormulaUnLet().transform(pred.getFormula());

		final Term dnf = SmtUtils.toDnf(mServices, mMngdScript, pred.getFormula(), mXnfConversion);
		return SmtUtils.getDisjuncts(dnf);
	}

	public IPredicate top() {
		return mTop;
	}

	public IPredicate bottom() {
		return mBottom;
	}

	public IPredicate predicate(final Term term) {
		return mFactory.newPredicate(term);
	}

	public IPredicate or(final IPredicate... operands) {
		return mFactory.or(mSimplification, operands);
	}

	public IPredicate or(final Collection<IPredicate> operands) {
		return mFactory.or(mSimplification, operands);
	}

	public IPredicate orT(final Term... operands) {
		return mFactory.orT(mSimplification, operands);
	}

	public IPredicate orT(final Collection<Term> operands) {
		return mFactory.orT(mSimplification, operands);
	}

	public IPredicate and(final IPredicate... operands) {
		return mFactory.and(mSimplification, operands);
	}

	public IPredicate and(final Collection<IPredicate> operands) {
		return mFactory.and(mSimplification, operands);
	}

	public IPredicate andT(final Term... operands) {
		return mFactory.andT(mSimplification, operands);
	}

	public IPredicate andT(final Collection<Term> operands) {
		return mFactory.andT(mSimplification, operands);
	}

	public Optional<Boolean> isFalse(final IPredicate pred) {
		// TODO: Use unifier instead of costly SMT check
		if (mBottom.equals(pred)) {
			return Optional.of(Boolean.TRUE);
		}
		final LBool result = SmtUtils.checkSatTerm(mMngdScript.getScript(), pred.getClosedFormula());
		return satAsBool(result).map(b -> !b);
	}

	public Optional<Boolean> implies(final IPredicate p1, final IPredicate p2) {
		// TODO: Use unifier instead of costly SMT check
		if (p1.equals(p2)) {
			return Optional.of(Boolean.TRUE);
		}
		final Script script = mMngdScript.getScript();
		final Term negImplTerm =
				SmtUtils.not(script, SmtUtils.implies(script, p1.getClosedFormula(), p2.getClosedFormula()));
		final LBool result = SmtUtils.checkSatTerm(script, negImplTerm);
		return satAsBool(result).map(b -> !b);
	}

	private static Optional<Boolean> satAsBool(final LBool solverResult) {
		switch (solverResult) {
		case SAT:
			return Optional.of(Boolean.TRUE);
		case UNSAT:
			return Optional.of(Boolean.FALSE);
		case UNKNOWN:
			return Optional.empty();
		default:
			throw new AssertionError("Missing case: " + solverResult);
		}
	}

	/**
	 * A {@link TermDomainOperationProvider} for {@link PredicateTransformer} that tries to eliminate all quantifiers
	 * during projection.
	 *
	 * It also logs only warning messages for PQE to avoid polluting the log.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class EliminatingTermDomainOperationProvider extends TermDomainOperationProvider {

		private final ILogger mPQELogger;

		public EliminatingTermDomainOperationProvider(final IUltimateServiceProvider services, final ILogger logger,
				final ManagedScript mgdScript) {
			super(services, mgdScript);
			mPQELogger = logger;
		}

		@Override
		public Term projectExistentially(final Set<TermVariable> varsToProjectAway, final Term constraint) {
			return newQuantifier(Script.EXISTS, varsToProjectAway, constraint);
		}

		@Override
		public Term projectUniversally(final Set<TermVariable> varsToProjectAway, final Term constraint) {
			return newQuantifier(Script.FORALL, varsToProjectAway, constraint);
		}

		private Term newQuantifier(final int quantifier, final Set<TermVariable> varsToQuantify, final Term term) {
			mStats.start(SifaStats.Key.TOOLS_QUANTIFIERELIM_TIME);
			final Term result = PartialQuantifierElimination.quantifier(mServices, mPQELogger, mMgdScript,
					SimplificationTechnique.NONE, mXnfConversion, quantifier, varsToQuantify, term);
			mStats.stop(SifaStats.Key.TOOLS_QUANTIFIERELIM_TIME);
			return result;
		}

	}

}
