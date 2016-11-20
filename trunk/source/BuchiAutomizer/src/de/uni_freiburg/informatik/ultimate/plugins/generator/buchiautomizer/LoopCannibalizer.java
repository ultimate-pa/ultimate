/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;

/**
 * Extract many predicates from a loop. Given a termination argument (given by a
 * honda predicate) we check for some shifts of the loop if the termination
 * argument is also sufficient compute interpolants.
 * 
 * @author Matthias Heizmann
 */
public class LoopCannibalizer {

	private final NestedLassoRun<CodeBlock, IPredicate> mCounterexample;
	private final BinaryStatePredicateManager mBspm;
	private final PredicateUnifier mPredicateUnifier;
	private final CfgSmtToolkit mCsToolkit;
	private final Set<IPredicate> mResultPredicates;
	private final Set<IPredicate> mOriginalLoopInterpolants;
	private final NestedWord<CodeBlock> mLoop;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final ICfgSymbolTable mBoogie2SmtSymbolTable;

	public LoopCannibalizer(final NestedLassoRun<CodeBlock, IPredicate> counterexample, final Set<IPredicate> loopInterpolants,
			final BinaryStatePredicateManager bspm, final PredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final InterpolationTechnique interpolation,
			final ICfgSymbolTable boogie2SmtSymbolTable, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mCounterexample = counterexample;
		mBspm = bspm;
		mPredicateUnifier = predicateUnifier;
		mCsToolkit = csToolkit;
		mOriginalLoopInterpolants = loopInterpolants;
		mResultPredicates = new HashSet<IPredicate>(loopInterpolants);
		mLoop = mCounterexample.getLoop().getWord();
		cannibalize(interpolation);
		mLogger.info(exitMessage());
	}

	private StringBuilder exitMessage() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mOriginalLoopInterpolants.size());
		sb.append(" predicates before loop cannibalization ");
		sb.append(mResultPredicates.size());
		sb.append(" predicates after loop cannibalization ");
		return sb;
	}

	private void cannibalize(final InterpolationTechnique interpolation) {
		final int startPosition;
		if (mLoop.isCallPosition(0) && !mLoop.isPendingCall(0)) {
			final int correspondingReturn = mLoop.getReturnPosition(0);
			startPosition = correspondingReturn;
		} else {
			startPosition = 1;
		}
		int i = startPosition;
		while (i < mLoop.length() - 1) {
			if (mLoop.isCallPosition(i) && !mLoop.isPendingCall(i)) {
				final int correspondingReturn = mLoop.getReturnPosition(i);
				i = correspondingReturn;
			} else {
				if (checkForNewPredicates(i)) {
					final NestedWord<CodeBlock> before = mLoop.getSubWord(0, i);
					final NestedWord<CodeBlock> after = mLoop.getSubWord(i + 1, mLoop.length() - 1);
					final NestedWord<CodeBlock> shifted = after.concatenate(before);
					final InterpolatingTraceChecker traceChecker = getTraceChecker(shifted, interpolation);
					final LBool loopCheck = traceChecker.isCorrect();
					if (loopCheck == LBool.UNSAT) {
						IPredicate[] loopInterpolants;
						loopInterpolants = traceChecker.getInterpolants();
						final Set<IPredicate> cannibalized = mPredicateUnifier.cannibalizeAll(false, loopInterpolants);
						mResultPredicates.addAll(cannibalized);
					} else {
						mLogger.info("termination argument not suffcient for all loop shiftings");
					}
				}
				i++;
			}
		}
	}

	private InterpolatingTraceChecker getTraceChecker(final NestedWord<CodeBlock> shifted, final InterpolationTechnique interpolation) {
		InterpolatingTraceChecker traceChecker;
		switch (interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			traceChecker = new InterpolatingTraceCheckerCraig(mBspm.getRankEqAndSi(), mBspm.getHondaPredicate(),
					new TreeMap<Integer, IPredicate>(), shifted, mCsToolkit, /*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					mServices, false, mPredicateUnifier, interpolation,
						true, mXnfConversionTechnique, mSimplificationTechnique, null);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			traceChecker = new TraceCheckerSpWp(mBspm.getRankEqAndSi(), mBspm.getHondaPredicate(),
					new TreeMap<Integer, IPredicate>(), shifted, mCsToolkit, /*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					UnsatCores.CONJUNCT_LEVEL,
					 true, mServices, false, mPredicateUnifier, interpolation,
						mCsToolkit.getManagedScript(), mXnfConversionTechnique, mSimplificationTechnique, null);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (traceChecker.getToolchainCanceledExpection() != null) {
			throw traceChecker.getToolchainCanceledExpection();
		}
		return traceChecker;
	}

	/**
	 * We check for new predicates if the CodeBlock at i uses a variable of the
	 * HondaPredicate, if the CodeBlock at i is a Return or the CodeBlock at i+1
	 * is a non-pending call.
	 */
	private boolean checkForNewPredicates(final int i) {
		if (codeBlockContainsVarOfHondaPredicate(mLoop.getSymbol(i))) {
			return true;
		}
		if (mLoop.isReturnPosition(i)) {
			assert !mLoop.isPendingReturn(i) : "not yet supported";
			return true;
		}
		if (mLoop.isCallPosition(i + 1)) {
			if (!mLoop.isPendingCall(i + 1)) {
				return true;
			}
		}
		return false;
	}

	private boolean codeBlockContainsVarOfHondaPredicate(final CodeBlock cb) {
		final Set<IProgramVar> hondaVars = mBspm.getHondaPredicate().getVars();
		final Set<IProgramVar> inVars = cb.getTransitionFormula().getInVars().keySet();
		if (!Collections.disjoint(hondaVars, inVars)) {
			return true;
		}
		final Set<IProgramVar> outVars = cb.getTransitionFormula().getOutVars().keySet();
		return !Collections.disjoint(hondaVars, outVars);
	}

	public Set<IPredicate> getResult() {
		return mResultPredicates;
	}

}
