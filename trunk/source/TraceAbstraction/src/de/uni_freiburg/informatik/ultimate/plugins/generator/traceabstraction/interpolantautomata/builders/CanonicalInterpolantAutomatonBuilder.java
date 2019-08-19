/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;

/**
 * Constructs the canonical interpolant automaton. Boolean flags determine if we also add selfloops in the initial and
 * final state. I think this construction is unsound if the precondition if not the "true" predicate.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CanonicalInterpolantAutomatonBuilder<CL, LETTER> extends CoverageAnalysis<CL>
		implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {

	private final boolean mSelfloopAtInitial = false;
	private final boolean mSelfloopAtFinal = true;

	private final NestedWordAutomaton<LETTER, IPredicate> mIA;
	protected final NestedWord<LETTER> mNestedWord;
	private final Map<Integer, Set<IPredicate>> mAlternativeCallPredecessors = new HashMap<>();

	public CanonicalInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final TracePredicates ipp, final List<CL> programPointSequence,
			final VpAlphabet<LETTER> alphabet, final CfgSmtToolkit csToolkit,
			final IEmptyStackStateFactory<IPredicate> predicateFactory, final ILogger logger,
			final IPredicateUnifier predicateUnifier, final NestedWord<LETTER> nestedWord) {
		super(services, ipp, programPointSequence, logger, predicateUnifier);
		mNestedWord = nestedWord;
		mIA = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), alphabet, predicateFactory);
	}

	@Override
	protected void processCodeBlock(final int i) {
		// interpolant after the CodeBlock
		final IPredicate successorInterpolant = mIpp.getPredicate(i + 1);
		if (!mIA.getStates().contains(successorInterpolant)) {
			assert (successorInterpolant != mIpp.getPostcondition());
			mIA.addState(false, false, successorInterpolant);
		}
		addTransition(i, i, i + 1);
	}

	protected void processCoveringResult(final int currentPosition, final int previousOccurrence, final LBool lbool) {
		if (lbool == LBool.UNSAT) {
			addTransition(currentPosition - 1, currentPosition - 1, previousOccurrence);
			addTransition(currentPosition, previousOccurrence, previousOccurrence + 1);
		}
	}

	@Override
	protected void postprocess() {
		if (mSelfloopAtInitial) {
			final IPredicate precond = mIpp.getPrecondition();
			for (final LETTER symbol : mIA.getVpAlphabet().getInternalAlphabet()) {
				mIA.addInternalTransition(precond, symbol, precond);
			}
			for (final LETTER symbol : mIA.getVpAlphabet().getCallAlphabet()) {
				mIA.addCallTransition(precond, symbol, precond);
			}
			for (final LETTER symbol : mIA.getVpAlphabet().getReturnAlphabet()) {
				mIA.addReturnTransition(precond, precond, symbol, precond);
				for (final Integer pos : mAlternativeCallPredecessors.keySet()) {
					for (final IPredicate hier : mAlternativeCallPredecessors.get(pos)) {
						mIA.addReturnTransition(precond, hier, symbol, precond);
					}
				}
			}
		}

		if (mSelfloopAtFinal) {
			final IPredicate postcond = mIpp.getPostcondition();
			for (final LETTER symbol : mIA.getVpAlphabet().getInternalAlphabet()) {
				mIA.addInternalTransition(postcond, symbol, postcond);
			}
			for (final LETTER symbol : mIA.getVpAlphabet().getCallAlphabet()) {
				mIA.addCallTransition(postcond, symbol, postcond);
			}
			for (final LETTER symbol : mIA.getVpAlphabet().getReturnAlphabet()) {
				mIA.addReturnTransition(postcond, postcond, symbol, postcond);
				for (final Integer pos : mAlternativeCallPredecessors.keySet()) {
					for (final IPredicate hier : mAlternativeCallPredecessors.get(pos)) {
						mIA.addReturnTransition(postcond, hier, symbol, postcond);
					}
				}
			}
		}
	}

	@Override
	protected void preprocess() {
		String interpolantAutomatonType = "Constructing canonical interpolant automaton";
		if (mSelfloopAtInitial) {
			interpolantAutomatonType += ", with selfloop in true state";
		}
		if (mSelfloopAtFinal) {
			interpolantAutomatonType += ", with selfloop in false state";
		}
		mLogger.info(interpolantAutomatonType);

		mIA.addState(true, false, mIpp.getPrecondition());
		mIA.addState(false, true, mIpp.getPostcondition());
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mIA;
	}

	private void addTransition(final int prePos, final int symbolPos, final int succPos) {
		final IPredicate pred = mIpp.getPredicate(prePos);
		final IPredicate succ = mIpp.getPredicate(succPos);
		final LETTER symbol = mNestedWord.getSymbol(symbolPos);
		if (mNestedWord.isCallPosition(symbolPos)) {
			mIA.addCallTransition(pred, symbol, succ);
			if (mIpp.getPredicate(prePos) != mIpp.getPredicate(symbolPos)) {
				addAlternativeCallPredecessor(symbolPos, mIpp.getPredicate(prePos));
			}
		} else if (mNestedWord.isReturnPosition(symbolPos)) {
			final int callPos = mNestedWord.getCallPosition(symbolPos);
			final IPredicate hier = mIpp.getPredicate(callPos);
			mIA.addReturnTransition(pred, hier, symbol, succ);
			addAlternativeReturnTransitions(pred, callPos, symbol, succ);
		} else {
			mIA.addInternalTransition(pred, symbol, succ);
		}
	}

	private void addAlternativeCallPredecessor(final int symbolPos, final IPredicate alternativeCallPredecessor) {
		Set<IPredicate> alts = mAlternativeCallPredecessors.get(symbolPos);
		if (alts == null) {
			alts = new HashSet<>();
			mAlternativeCallPredecessors.put(symbolPos, alts);
		}
		alts.add(alternativeCallPredecessor);
	}

	private void addAlternativeReturnTransitions(final IPredicate pred, final int callPos, final LETTER symbol,
			final IPredicate succ) {
		if (mAlternativeCallPredecessors.get(callPos) == null) {
			return;
		}
		// 2016-05-18 Matthias: Do not add alternative returns, this seems to be expensive
		// and I am too lazy to construct another IHoaretripleChecker for these few checks.
		// for (IPredicate hier : mAlternativeCallPredecessors.get(callPos)) {
		// LBool isInductive = mCsToolkit.isInductiveReturn(pred, hier, (Return) symbol, succ);
		// mLogger.debug("Trying to add alternative call Predecessor");
		// if (isInductive == Script.LBool.UNSAT) {
		// mIA.addReturnTransition(pred, hier, symbol, succ);
		// mLogger.debug("Added return from alternative call Pred");
		// }
		// }
	}

}
