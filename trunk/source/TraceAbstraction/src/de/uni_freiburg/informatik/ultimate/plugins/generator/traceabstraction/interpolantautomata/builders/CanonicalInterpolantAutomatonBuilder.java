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
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;

/**
 * Constructs the canonical interpolant automaton. Boolean flags determine if we also add selfloops in the initial and
 * final state. I think this construction is unsound if the precondition if not the "true" predicate.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CanonicalInterpolantAutomatonBuilder extends CoverageAnalysis
		implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {

	private final NestedWordAutomaton<CodeBlock, IPredicate> mIA;

	private final boolean mSelfloopAtInitial = false;
	private final boolean mSelfloopAtFinal = true;

	private final SmtManager mSmtManager;

	private final Map<Integer, Set<IPredicate>> mAlternativeCallPredecessors = new HashMap<Integer, Set<IPredicate>>();

	public CanonicalInterpolantAutomatonBuilder(IUltimateServiceProvider services,
			IInterpolantGenerator interpolantGenerator, List<ProgramPoint> programPointSequence,
			InCaReAlphabet<CodeBlock> alphabet, SmtManager smtManager, StateFactory<IPredicate> predicateFactory,
			ILogger logger) {
		super(services, interpolantGenerator, programPointSequence, logger);
		mIA = new NestedWordAutomaton<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				alphabet.getInternalAlphabet(), alphabet.getCallAlphabet(), alphabet.getReturnAlphabet(),
				predicateFactory);
		mSmtManager = smtManager;
	}

	@Override
	protected void processCodeBlock(int i) {
		// interpolant after the CodeBlock
		final IPredicate successorInterpolant = mIPP.getInterpolant(i + 1);
		if (!mIA.getStates().contains(successorInterpolant)) {
			assert (successorInterpolant != mInterpolantGenerator.getPostcondition());
			mIA.addState(false, false, successorInterpolant);
		}
		addTransition(i, i, i + 1);
	}

	protected void processCoveringResult(int currentPosition, int previousOccurrence, LBool lbool) {
		if (lbool == LBool.UNSAT) {
			addTransition(currentPosition - 1, currentPosition - 1, previousOccurrence);
			addTransition(currentPosition, previousOccurrence, previousOccurrence + 1);
		}
	}

	@Override
	protected void postprocess() {
		if (mSelfloopAtInitial) {
			final IPredicate precond = mInterpolantGenerator.getPrecondition();
			for (final CodeBlock symbol : mIA.getInternalAlphabet()) {
				mIA.addInternalTransition(precond, symbol, precond);
			}
			for (final CodeBlock symbol : mIA.getCallAlphabet()) {
				mIA.addCallTransition(precond, symbol, precond);
			}
			for (final CodeBlock symbol : mIA.getReturnAlphabet()) {
				mIA.addReturnTransition(precond, precond, symbol, precond);
				for (final Integer pos : mAlternativeCallPredecessors.keySet()) {
					for (final IPredicate hier : mAlternativeCallPredecessors.get(pos)) {
						mIA.addReturnTransition(precond, hier, symbol, precond);
					}
				}
			}
		}

		if (mSelfloopAtFinal) {
			final IPredicate postcond = mInterpolantGenerator.getPostcondition();
			for (final CodeBlock symbol : mIA.getInternalAlphabet()) {
				mIA.addInternalTransition(postcond, symbol, postcond);
			}
			for (final CodeBlock symbol : mIA.getCallAlphabet()) {
				mIA.addCallTransition(postcond, symbol, postcond);
			}
			for (final CodeBlock symbol : mIA.getReturnAlphabet()) {
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

		mIA.addState(true, false, mInterpolantGenerator.getPrecondition());
		mIA.addState(false, true, mInterpolantGenerator.getPostcondition());
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mIA;
	}

	private void addTransition(int prePos, int symbolPos, int succPos) {
		final IPredicate pred = mIPP.getInterpolant(prePos);
		final IPredicate succ = mIPP.getInterpolant(succPos);
		final CodeBlock symbol = (CodeBlock) mNestedWord.getSymbol(symbolPos);
		if (mNestedWord.isCallPosition(symbolPos)) {
			mIA.addCallTransition(pred, symbol, succ);
			if (mIPP.getInterpolant(prePos) != mIPP.getInterpolant(symbolPos)) {
				addAlternativeCallPredecessor(symbolPos, mIPP.getInterpolant(prePos));
			}
		} else if (mNestedWord.isReturnPosition(symbolPos)) {
			final int callPos = mNestedWord.getCallPosition(symbolPos);
			final IPredicate hier = mIPP.getInterpolant(callPos);
			mIA.addReturnTransition(pred, hier, symbol, succ);
			addAlternativeReturnTransitions(pred, callPos, symbol, succ);
		} else {
			mIA.addInternalTransition(pred, symbol, succ);
		}
	}

	private void addAlternativeCallPredecessor(int symbolPos, IPredicate alternativeCallPredecessor) {
		Set<IPredicate> alts = mAlternativeCallPredecessors.get(symbolPos);
		if (alts == null) {
			alts = new HashSet<IPredicate>();
			mAlternativeCallPredecessors.put(symbolPos, alts);
		}
		alts.add(alternativeCallPredecessor);
	}

	private void addAlternativeReturnTransitions(IPredicate pred, int callPos, CodeBlock symbol, IPredicate succ) {
		if (mAlternativeCallPredecessors.get(callPos) == null) {
			return;
		}
		// 2016-05-18 Matthias: Do not add alternative returns, this seems to be expensive
		// and I am too lazy to construct another IHoaretripleChecker for these few checks.
		// for (IPredicate hier : mAlternativeCallPredecessors.get(callPos)) {
		// LBool isInductive = mSmtManager.isInductiveReturn(pred, hier, (Return) symbol, succ);
		// mLogger.debug("Trying to add alternative call Predecessor");
		// if (isInductive == Script.LBool.UNSAT) {
		// mIA.addReturnTransition(pred, hier, symbol, succ);
		// mLogger.debug("Added return from alternative call Pred");
		// }
		// }
	}

}
