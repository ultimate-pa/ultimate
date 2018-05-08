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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.BasicCallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.BasicReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * Checks the relevance of a <code>CodeBlock</code> with respect to a pre- and a
 * postcondition. The check is reduced to a Hoare triple check.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class FaultLocalizationRelevanceChecker {
	
	private static final boolean mUseUnsatCores = false;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	/**
	 * Statement relevance information for fault localization.
	 * 
	 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
	 */
	public enum ERelevanceStatus {
		Sat,
		InUnsatCore,
		NotInUnsatCore,
		unknown
	}
	
	/**
	 * Used by Fault Localization to compute the relevance of statements.
	 * 
	 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
	 */
	private class FaultLocalizationHoareTripleChecker
			extends IncrementalHoareTripleChecker {
		
		public FaultLocalizationHoareTripleChecker(final CfgSmtToolkit csToolkit) {
			super(csToolkit, false);
		}
		
		@Override
		public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
			prepareAssertionStackAndAddTransition(act);
			prepareAssertionStackAndAddPrecondition(pre);
			prepareAssertionStackAndAddPostcond(post);
			return checkValidity();
		}
		
		@Override
		public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
			prepareAssertionStackAndAddTransition(act);
			prepareAssertionStackAndAddPrecondition(pre);
			prepareAssertionStackAndAddPostcond(post);
			return checkValidity();
		}
		
		@Override
		public Validity checkReturn(final IPredicate linPre, final IPredicate hierPre,
				final IReturnAction act, final IPredicate postcond) {
			prepareAssertionStackAndAddTransition(act);
			prepareAssertionStackAndAddPrecondition(linPre);
			prepareAssertionStackAndAddHierpred(hierPre);
			prepareAssertionStackAndAddPostcond(postcond);
			return checkValidity();
		}
		
		public boolean doesUnsatCoreContainTransition() {
			final Term[] unsatCore = mManagedScript.getUnsatCore(this);
			for (final Term term : unsatCore) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getApplicationString().equals(
						IncrementalHoareTripleChecker.ID_TRANSITION_FORMULA)) {
					return true;
				}
			}
			return false;
		}
	}
	
	private final FaultLocalizationHoareTripleChecker mHoareTripleChecker;
	private final ManagedScript mManagedScript;
	
	
	public FaultLocalizationRelevanceChecker(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mHoareTripleChecker = new FaultLocalizationHoareTripleChecker(csToolkit);
		mManagedScript = csToolkit.getManagedScript();
	}
	
	public ERelevanceStatus relevanceInternal(final IPredicate pre,
			final IInternalAction act, final IPredicate post) {
		final ERelevanceStatus result;
		if (mUseUnsatCores) {
			final Validity val = mHoareTripleChecker.checkInternal(pre, act, post);
			result = getResult(val, mHoareTripleChecker);
		} else {
			result = computeRelevancyInternalWithoutUnsatCores(pre, act, post);
		}
		mHoareTripleChecker.clearAssertionStack();
		return result;
	}

	private ERelevanceStatus computeRelevancyInternalWithoutUnsatCores(final IPredicate pre, final IInternalAction act,
			final IPredicate post) {
		final ERelevanceStatus result;
		final Validity havocRes = mHoareTripleChecker.checkInternal(pre, constructHavocedInternalAction(mServices, act, mManagedScript), post);
		switch (havocRes) {
		case INVALID: {
			final Validity nomalRes = mHoareTripleChecker.checkInternal(pre, act, post);
			switch (nomalRes) {
			case INVALID:
				result = ERelevanceStatus.Sat;
				break;
			case NOT_CHECKED:
			case UNKNOWN:
				result = ERelevanceStatus.unknown;
				break;
			case VALID:
				result = ERelevanceStatus.InUnsatCore;
				break;
			default:
				throw new AssertionError();
			}
			break;
		}
		case NOT_CHECKED:
		case UNKNOWN:
			result = ERelevanceStatus.unknown;
			break;
		case VALID:
			result = ERelevanceStatus.NotInUnsatCore;
			break;
		default:
			throw new AssertionError();
		}
		return result;
	}
	
	public ERelevanceStatus relevanceCall(final IPredicate pre,
			final ICallAction call, final IPredicate post) {
		final ERelevanceStatus result;
		if (mUseUnsatCores) {
			final Validity val = mHoareTripleChecker.checkCall(pre, call, post);
			result = getResult(val, mHoareTripleChecker);
		} else {
			result = computeRelevancyCallWithoutUnsatCores(pre, call, post);
		}
		mHoareTripleChecker.clearAssertionStack();
		return result;
	}
	
	private ERelevanceStatus computeRelevancyCallWithoutUnsatCores(final IPredicate pre, final ICallAction act,
			final IPredicate post) {
		final ERelevanceStatus result;
		final Validity havocRes = mHoareTripleChecker.checkCall(pre, constructHavocedCallAction(mServices, act, mManagedScript), post);
		switch (havocRes) {
		case INVALID: {
			final Validity nomalRes = mHoareTripleChecker.checkCall(pre, act, post);
			switch (nomalRes) {
			case INVALID:
				result = ERelevanceStatus.Sat;
				break;
			case NOT_CHECKED:
			case UNKNOWN:
				result = ERelevanceStatus.unknown;
				break;
			case VALID:
				result = ERelevanceStatus.InUnsatCore;
				break;
			default:
				throw new AssertionError();
			}
			break;
		}
		case NOT_CHECKED:
		case UNKNOWN:
			result = ERelevanceStatus.unknown;
			break;
		case VALID:
			result = ERelevanceStatus.NotInUnsatCore;
			break;
		default:
			throw new AssertionError();
		}
		return result;
	}
	
	public ERelevanceStatus relevanceReturn(final IPredicate returnPre,
			final IPredicate callPre,
			final IReturnAction ret, final IPredicate post) {
		final ERelevanceStatus result;
		if (mUseUnsatCores) {
			final Validity val = mHoareTripleChecker.checkReturn(returnPre, 
					callPre, ret, post);
			result = getResult(val, mHoareTripleChecker);
		} else {
			result = computeRelevancyReturnWithoutUnsatCores(returnPre, callPre, ret, post);
		}
		mHoareTripleChecker.clearAssertionStack();
		return result;
	}
	
	private ERelevanceStatus computeRelevancyReturnWithoutUnsatCores(final IPredicate pre, final IPredicate hier,
			final IReturnAction act, final IPredicate post) {
		final ERelevanceStatus result;
		final Validity havocRes = mHoareTripleChecker.checkReturn(pre, hier, constructHavocedReturnAction(mServices, act, mManagedScript), post);
		switch (havocRes) {
		case INVALID: {
			final Validity nomalRes = mHoareTripleChecker.checkReturn(pre, hier, act, post);
			switch (nomalRes) {
			case INVALID:
				result = ERelevanceStatus.Sat;
				break;
			case NOT_CHECKED:
			case UNKNOWN:
				result = ERelevanceStatus.unknown;
				break;
			case VALID:
				result = ERelevanceStatus.InUnsatCore;
				break;
			default:
				throw new AssertionError();
			}
			break;
		}
		case NOT_CHECKED:
		case UNKNOWN:
			result = ERelevanceStatus.unknown;
			break;
		case VALID:
			result = ERelevanceStatus.NotInUnsatCore;
			break;
		default:
			throw new AssertionError();
		}
		return result;
	}

	
	/**
	 * @param val validity status from Hoare triple check
	 * @param hoareTripleChecker
	 * @return relevance
	 */
	private ERelevanceStatus getResult(final Validity val,
			final FaultLocalizationHoareTripleChecker hoareTripleChecker) {
		final ERelevanceStatus result;
		switch (val) {
			case INVALID: // satisfiable
				result = ERelevanceStatus.Sat;
				break;
				
			case VALID: // unsatisfiable, check unsat core
				final boolean ucContainsTransition = hoareTripleChecker.doesUnsatCoreContainTransition();
				result = ucContainsTransition
						? ERelevanceStatus.InUnsatCore
						: ERelevanceStatus.NotInUnsatCore;
				break;
				
			case UNKNOWN:
				result = ERelevanceStatus.unknown;
				break;
				
			case NOT_CHECKED:
			default:
				throw new IllegalArgumentException(String.format(
						"Hoare triple check returned status '%s'.", val));
		}
		return result;
	}
	
	public HoareTripleCheckerStatisticsGenerator getHoareTripleCheckerStatistics() {
		return mHoareTripleChecker.getEdgeCheckerBenchmark();
	}
	
	public IInternalAction constructHavocedInternalAction(final IUltimateServiceProvider services,
			final IInternalAction act, final ManagedScript mgdScript) {
		return new BasicInternalAction(act.getPrecedingProcedure(), act.getSucceedingProcedure(),
				constructHavoc(services, act.getTransformula(), mgdScript));
	}

	public ICallAction constructHavocedCallAction(final IUltimateServiceProvider services, final ICallAction act,
			final ManagedScript mgdScript) {
		return new BasicCallAction(act.getPrecedingProcedure(), act.getSucceedingProcedure(),
				constructHavoc(services, act.getLocalVarsAssignment(), mgdScript));
	}

	public IReturnAction constructHavocedReturnAction(final IUltimateServiceProvider services,
			final IReturnAction act, final ManagedScript mgdScript) {
		return new BasicReturnAction(act.getPrecedingProcedure(), act.getSucceedingProcedure(),
				constructHavoc(services, act.getAssignmentOfReturn(), mgdScript),
				constructHavoc(services, act.getLocalVarsAssignmentOfCall(), mgdScript));
	}
	
	public UnmodifiableTransFormula constructHavoc(final IUltimateServiceProvider services,
			final UnmodifiableTransFormula tf, final ManagedScript mgdScript) {
		UnmodifiableTransFormula result;
		if (containsArraySort(tf.getFormula())) {
			result = TransFormulaUtils.computeGuardedHavoc(tf, mgdScript, services, mLogger, true); 
		} else {
			result = TransFormulaUtils.constructHavoc(tf, mgdScript);
		}
		return result;
	}

	private static boolean containsArraySort(final Term formula) {
		final Predicate<Term> hasArraySort = (x -> SmtSortUtils.isArraySort(x.getSort()));
		return new SubtermPropertyChecker(hasArraySort).isPropertySatisfied(formula);
	}
}