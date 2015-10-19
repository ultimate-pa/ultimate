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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

/**
 * Extract many predicates from a loop. Given a termination argument (given by a
 * honda predicate) we check for some shifts of the loop if the termination
 * argument is also sufficient compute interpolants.
 * 
 * @author Matthias Heizmann
 */
public class LoopCannibalizer {

	private final NestedLassoRun<CodeBlock, IPredicate> m_Counterexample;
	private final BinaryStatePredicateManager m_Bspm;
	private final PredicateUnifier m_PredicateUnifier;
	private final SmtManager m_SmtManager;
	private final BuchiModGlobalVarManager m_buchiModGlobalVarManager;
	private final Set<IPredicate> m_ResultPredicates;
	private final Set<IPredicate> m_OriginalLoopInterpolants;
	private NestedWord<CodeBlock> m_Loop;

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public LoopCannibalizer(NestedLassoRun<CodeBlock, IPredicate> counterexample, Set<IPredicate> loopInterpolants,
			BinaryStatePredicateManager bspm, PredicateUnifier predicateUnifier, SmtManager smtManager,
			BuchiModGlobalVarManager buchiModGlobalVarManager, INTERPOLATION interpolation,
			IUltimateServiceProvider services) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Counterexample = counterexample;
		m_Bspm = bspm;
		m_PredicateUnifier = predicateUnifier;
		m_SmtManager = smtManager;
		m_buchiModGlobalVarManager = buchiModGlobalVarManager;
		m_OriginalLoopInterpolants = loopInterpolants;
		m_ResultPredicates = new HashSet<IPredicate>(loopInterpolants);
		m_Loop = m_Counterexample.getLoop().getWord();
		cannibalize(interpolation);
		mLogger.info(exitMessage());
	}

	private StringBuilder exitMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append(m_OriginalLoopInterpolants.size());
		sb.append(" predicates before loop cannibalization ");
		sb.append(m_ResultPredicates.size());
		sb.append(" predicates after loop cannibalization ");
		return sb;
	}

	private void cannibalize(INTERPOLATION interpolation) {
		final int startPosition;
		if (m_Loop.isCallPosition(0) && !m_Loop.isPendingCall(0)) {
			int correspondingReturn = m_Loop.getReturnPosition(0);
			startPosition = correspondingReturn;
		} else {
			startPosition = 1;
		}
		int i = startPosition;
		while (i < m_Loop.length() - 1) {
			if (m_Loop.isCallPosition(i) && !m_Loop.isPendingCall(i)) {
				int correspondingReturn = m_Loop.getReturnPosition(i);
				i = correspondingReturn;
			} else {
				if (checkForNewPredicates(i)) {
					NestedWord<CodeBlock> before = m_Loop.subWord(0, i);
					NestedWord<CodeBlock> after = m_Loop.subWord(i + 1, m_Loop.length() - 1);
					NestedWord<CodeBlock> shifted = after.concatenate(before);
					InterpolatingTraceChecker traceChecker = getTraceChecker(shifted, interpolation);
					LBool loopCheck = traceChecker.isCorrect();
					if (loopCheck == LBool.UNSAT) {
						IPredicate[] loopInterpolants;
						loopInterpolants = traceChecker.getInterpolants();
						Set<IPredicate> cannibalized = m_PredicateUnifier.cannibalizeAll(false, loopInterpolants);
						m_ResultPredicates.addAll(cannibalized);
					} else {
						mLogger.info("termination argument not suffcient for all loop shiftings");
					}
				}
				i++;
			}
		}
	}

	private InterpolatingTraceChecker getTraceChecker(NestedWord<CodeBlock> shifted, INTERPOLATION interpolation) {
		InterpolatingTraceChecker traceChecker;
		switch (interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			traceChecker = new InterpolatingTraceCheckerCraig(m_Bspm.getRankEqAndSi(), m_Bspm.getHondaPredicate(),
					new TreeMap<Integer, IPredicate>(), shifted, m_SmtManager, m_buchiModGlobalVarManager,
					/*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices, false, m_PredicateUnifier,
						interpolation);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			traceChecker = new TraceCheckerSpWp(m_Bspm.getRankEqAndSi(), m_Bspm.getHondaPredicate(),
					new TreeMap<Integer, IPredicate>(), shifted, m_SmtManager, m_buchiModGlobalVarManager,
					/*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					 UnsatCores.CONJUNCT_LEVEL, true, mServices, false, m_PredicateUnifier,
						interpolation);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (traceChecker.getToolchainCancelledExpection() != null) {
			throw traceChecker.getToolchainCancelledExpection();
		}
		return traceChecker;
	}

	/**
	 * We check for new predicates if the CodeBlock at i uses a variable of the
	 * HondaPredicate, if the CodeBlock at i is a Return or the CodeBlock at i+1
	 * is a non-pending call.
	 */
	private boolean checkForNewPredicates(int i) {
		if (codeBlockContainsVarOfHondaPredicate(m_Loop.getSymbol(i))) {
			return true;
		}
		if (m_Loop.isReturnPosition(i)) {
			assert !m_Loop.isPendingReturn(i) : "not yet supported";
			return true;
		}
		if (m_Loop.isCallPosition(i + 1)) {
			if (!m_Loop.isPendingCall(i + 1)) {
				return true;
			}
		}
		return false;
	}

	private boolean codeBlockContainsVarOfHondaPredicate(CodeBlock cb) {
		Set<BoogieVar> hondaVars = m_Bspm.getHondaPredicate().getVars();
		Set<BoogieVar> inVars = cb.getTransitionFormula().getInVars().keySet();
		if (!Collections.disjoint(hondaVars, inVars)) {
			return true;
		}
		Set<BoogieVar> outVars = cb.getTransitionFormula().getOutVars().keySet();
		if (!Collections.disjoint(hondaVars, outVars)) {
			return true;
		}
		return false;
	}

	public Set<IPredicate> getResult() {
		return m_ResultPredicates;
	}

}
