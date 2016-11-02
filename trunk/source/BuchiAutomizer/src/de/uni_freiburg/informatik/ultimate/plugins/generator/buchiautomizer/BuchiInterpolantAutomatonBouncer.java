/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Given a lasso annotated with predicates, construct an interpolant automaton
 * that is nearly determinisitic.
 * 
 * @author Matthias Heizmann
 * 
 */
public class BuchiInterpolantAutomatonBouncer extends AbstractInterpolantAutomaton {

	@Deprecated
	private final Set<IPredicate> mInputStemPredicates = new HashSet<IPredicate>();
	@Deprecated
	private final Set<IPredicate> mInputLoopPredicates = new HashSet<IPredicate>();

	/**
	 * Input predicates without auxiliary rank variables.
	 */
	private final Set<IPredicate> mInputAuxFreePredicates = new HashSet<IPredicate>();

	/**
	 * Input predicates with auxiliary rank variables.
	 */
	private final Set<IPredicate> mInputWithAuxPredicates = new HashSet<IPredicate>();

	// private final IPredicate mHondaPredicate;

	private final CodeBlock mHondaEntererStem;
	private final CodeBlock mHondaEntererLoop;

	private final boolean mScroogeNondeterminismStem;
	private final boolean mScroogeNondeterminismLoop;
	private final boolean mHondaBouncerStem;
	private final boolean mHondaBouncerLoop;

	private final BinaryStatePredicateManager mBspm;

	private final Map<Set<IPredicate>, IPredicate> mStemInputPreds2ResultPreds = new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> mStemResPred2InputPreds = new HashRelation<IPredicate, IPredicate>();

	private final Map<Set<IPredicate>, IPredicate> mLoopInputPreds2ResultPreds = new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> mLoopResPred2InputPreds = new HashRelation<IPredicate, IPredicate>();

	private final Map<Set<IPredicate>, IPredicate> mAcceptingInputPreds2ResultPreds = new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> mAcceptingResPred2InputPreds = new HashRelation<IPredicate, IPredicate>();

	private final Map<Set<IPredicate>, IPredicate> mRankEqInputPreds2ResultPreds = new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> mRankEqResPred2InputPreds = new HashRelation<IPredicate, IPredicate>();

	private final Map<Set<IPredicate>, IPredicate> mWithoutAuxInputPreds2ResultPreds = new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> mWithoutAuxPred2InputPreds = new HashRelation<IPredicate, IPredicate>();

	private final PredicateUnifier mStemPU;
	private final PredicateUnifier mLoopPU;
	private final PredicateUnifier mAcceptingPU;

	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	
	private final PredicateFactory mPredicateFactory;

	public BuchiInterpolantAutomatonBouncer(final SmtManager smtManager, final PredicateFactory predicateFactory, final BinaryStatePredicateManager bspm,
			final BuchiHoareTripleChecker bhtc, final boolean emtpyStem, final Set<IPredicate> stemInterpolants,
			final Set<IPredicate> loopInterpolants, final CodeBlock hondaEntererStem, final CodeBlock hondaEntererLoop,
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction, final boolean scroogeNondeterminismStem,
			final boolean scroogeNondeterminismLoop, final boolean hondaBouncerStem, final boolean hondaBouncerLoop,
			final PredicateFactoryForInterpolantAutomata predicateFactoryFia, final PredicateUnifier stemPU, final PredicateUnifier loopPU,
			final IPredicate falsePredicate, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique, 
			final Boogie2SmtSymbolTable symbolTable) {
		super(services, smtManager, bhtc, false, abstraction, falsePredicate, null, services.getLoggingService().getLogger(
				Activator.PLUGIN_ID));
		mServices = services;
		mPredicateFactory = predicateFactory;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mBspm = bspm;
		mStemPU = new PredicateUnifier(mServices, mSmtManager.getManagedScript(), mPredicateFactory, symbolTable, mSimplificationTechnique, mXnfConversionTechnique, falsePredicate);
		mLoopPU = new PredicateUnifier(mServices, mSmtManager.getManagedScript(), mPredicateFactory, symbolTable, mSimplificationTechnique, mXnfConversionTechnique, falsePredicate);
		mAcceptingPU = new PredicateUnifier(mServices, mSmtManager.getManagedScript(), mPredicateFactory, symbolTable, mSimplificationTechnique, mXnfConversionTechnique, falsePredicate);
		IPredicate initialPredicate;
		if (emtpyStem) {
			final Set<IPredicate> empty = Collections.emptySet();
			initialPredicate = getOrConstructAcceptingPredicate(empty, true);
		} else {
			initialPredicate = getOrConstructStemPredicate(Collections.singleton(mBspm.getStemPrecondition()), true);
		}

		initializeConstruction(emtpyStem, bspm, stemInterpolants, loopInterpolants);
		mHondaEntererStem = hondaEntererStem;
		mHondaEntererLoop = hondaEntererLoop;
		/**
		 * Allow a some special nondeterministic transitions. For this
		 * additional transition the - predecessor is some stem predicate - the
		 * letter is mHondaEntererStem - the successor is the honda state
		 */
		mScroogeNondeterminismStem = scroogeNondeterminismStem;
		mScroogeNondeterminismLoop = scroogeNondeterminismLoop;
		/**
		 * If set, the nondeterministic transition from the stem predicates into
		 * the honda is only allowed for the letter mHondaEntererStem
		 */
		mHondaBouncerStem = hondaBouncerStem;
		/**
		 * If set, a transition from the stem predicates may only go to the
		 * honda if the letter is mHondaEntererLoop
		 */
		mHondaBouncerLoop = hondaBouncerLoop;
		mLogger.info(startMessage());
	}

	private void initializeConstruction(final boolean emtpyStem, final BinaryStatePredicateManager bspm,
			final Set<IPredicate> stemInterpolants, final Set<IPredicate> loopInterpolants) {
		final IPredicate precondition = bspm.getStemPrecondition();
		if (!emtpyStem) {
			mInputStemPredicates.add(precondition);
			for (final IPredicate stemPredicate : stemInterpolants) {
				if (!mInputStemPredicates.contains(stemPredicate)) {
					mInputStemPredicates.add(stemPredicate);
				}
			}
		}
		mInputAuxFreePredicates.add(mBspm.getSiConjunction());
		for (final IPredicate loopPredicate : loopInterpolants) {
			if (!mInputLoopPredicates.contains(loopPredicate)) {
				mInputLoopPredicates.add(loopPredicate);
			}
			if (bspm.containsOldRankVariable(loopPredicate)) {
				mInputWithAuxPredicates.add(loopPredicate);
			} else {
				mInputAuxFreePredicates.add(loopPredicate);
			}
		}
	}

	@Override
	protected String startMessage() {
		final StringBuilder sb = new StringBuilder();
		if (mScroogeNondeterminismStem || mScroogeNondeterminismLoop) {
			sb.append("Defining Buchi interpolant automaton with scrooge nondeterminism ");
			if (mScroogeNondeterminismStem) {
				sb.append("in stem");
				if (mScroogeNondeterminismLoop) {
					sb.append("in loop");
				}
			} else {
				sb.append("in loop");
			}
		} else {
			sb.append("Defining deterministic Buchi interpolant automaton ");
		}
		sb.append(mHondaBouncerStem ? "with " : "without ");
		sb.append("honda bouncer for stem and ");
		sb.append(mHondaBouncerLoop ? "with " : "without ");
		sb.append("honda bouncer for loop.");
		sb.append(mInputStemPredicates.size()).append(" stem predicates ");
		sb.append(mInputLoopPredicates.size()).append(" loop predicates ");
		return sb.toString();
	}

	@Override
	protected String switchToReadonlyMessage() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Switched to read-only mode: Buchi interpolant automaton has ");
		sb.append(mAlreadyConstrucedAutomaton.size()).append(" states ");
		sb.append(mStemResPred2InputPreds.getDomain().size()).append(" stem states ");
		sb.append(mLoopResPred2InputPreds.getDomain().size()).append(" non-accepting loop states ");
		sb.append(mAcceptingResPred2InputPreds.getDomain().size()).append(" accepting loop states ");
		return sb.toString();
	}
	
	@Override
	protected String switchToOnTheFlyConstructionMessage() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Switched to OnTheFlyConstruction mode: Buchi interpolant automaton has ");
		sb.append(mAlreadyConstrucedAutomaton.size()).append(" states ");
		sb.append(mStemResPred2InputPreds.getDomain().size()).append(" stem states ");
		sb.append(mLoopResPred2InputPreds.getDomain().size()).append(" non-accepting loop states ");
		sb.append(mAcceptingResPred2InputPreds.getDomain().size()).append(" accepting loop states ");
		return sb.toString();
	}

	@Override
	protected void computeSuccs(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter, final SuccessorComputationHelper sch) {
		if (isPredHierLetterFalse(resPred, resHier, letter, sch)) {
			if (!mAlreadyConstrucedAutomaton.contains(mIaFalseState)) {
				mAlreadyConstrucedAutomaton.addState(false, true, mIaFalseState);
				mLogger.debug("BenchmarkResult: Transition to False Predicate");
			}
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
		} else if (isFalseSucc(resPred, resHier, letter, sch)) {
			if (!mAlreadyConstrucedAutomaton.contains(mIaFalseState)) {
				mAlreadyConstrucedAutomaton.addState(false, true, mIaFalseState);
				mLogger.debug("BenchmarkResult: Transition to False Predicate");
			}
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
		} else if (mStemResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsStem(resPred, resHier, letter, sch);
		} else if (mAcceptingResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsLoop(resPred, resHier, letter, sch);
		} else if (mLoopResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsLoop(resPred, resHier, letter, sch);
		} else {
			throw new AssertionError("unknown state");
		}
		sch.reportSuccsComputed(resPred, resHier, letter);
	}

	private boolean isPredHierLetterFalse(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		final boolean result;
		if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			result = true;
		} else if (sch.isLinearPredecessorFalse(resPred)) {
			result = true;
		} else if (sch.isHierarchicalPredecessorFalse(resHier)) {
			result = true;
		} else {
			result = false;
		}
		return result;
	}

	private boolean isFalseSucc(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter, final SuccessorComputationHelper sch) {
		final boolean result;
		final Validity validity = sch.computeSuccWithSolver(resPred, resHier, letter, mIaFalseState);
		if (validity == Validity.VALID) {
			result = true;
		} else {
			result = false;
		}
		return result;
	}

	private void computeSuccsStem(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		IPredicate acceptingSucc;
		if (mayEnterAcceptingFromStem(letter)) {
			acceptingSucc = addAcceptingSuccStem(resPred, resHier, letter, sch);
		} else {
			acceptingSucc = null;
		}
		if (acceptingSucc == null || mScroogeNondeterminismStem) {
			addNonAcceptingSuccStem(resPred, resHier, letter, sch);
		}
	}

	private IPredicate addAcceptingSuccStem(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccsWithoutAux = new HashSet<IPredicate>();
		for (final IPredicate succCand : mInputAuxFreePredicates) {
			final Validity validity = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (validity == Validity.VALID) {
				inputSuccsWithoutAux.add(succCand);
			}
		}
		final IPredicate resSucc = getOrConstructAcceptingPredicate(inputSuccsWithoutAux, false);
		sch.addTransition(resPred, resHier, letter, resSucc);
		return resSucc;
	}

	private IPredicate getOrConstructAcceptingPredicate(final Set<IPredicate> inputSuccsWithoutAuxVar, final boolean isInitial) {
		final IPredicate withoutAux = getOrConstructPredicate(inputSuccsWithoutAuxVar, mStemPU,
				mWithoutAuxInputPreds2ResultPreds, mWithoutAuxPred2InputPreds);
		final Set<IPredicate> inputSuccsRankDecreaseAndBound = new HashSet<IPredicate>(inputSuccsWithoutAuxVar);
		inputSuccsRankDecreaseAndBound.add(mBspm.getRankDecreaseAndBound());
		final IPredicate rankDecreaseAndBound = getOrConstructPredicate(inputSuccsRankDecreaseAndBound, mAcceptingPU,
				mAcceptingInputPreds2ResultPreds, mAcceptingResPred2InputPreds);
		final Set<IPredicate> inputSuccsRankEquality = new HashSet<IPredicate>(inputSuccsWithoutAuxVar);
		inputSuccsRankEquality.add(mBspm.getRankEquality());
		final IPredicate rankEquality = getOrConstructPredicate(inputSuccsRankEquality, mLoopPU,
				mRankEqInputPreds2ResultPreds, mRankEqResPred2InputPreds);
		if (!mAlreadyConstrucedAutomaton.contains(rankDecreaseAndBound)) {
			mAlreadyConstrucedAutomaton.addState(isInitial, true, rankDecreaseAndBound);
		}
		((BuchiHoareTripleChecker) mIHoareTripleChecker).putDecreaseEqualPair(rankDecreaseAndBound, rankEquality);
		return rankDecreaseAndBound;
	}

	private IPredicate getOrConstructStemPredicate(final Set<IPredicate> inputSuccs, final boolean isInitial) {
		final IPredicate resSucc = getOrConstructPredicate(inputSuccs, mStemPU, mStemInputPreds2ResultPreds,
				mStemResPred2InputPreds);
		if (!mAlreadyConstrucedAutomaton.contains(resSucc)) {
			mAlreadyConstrucedAutomaton.addState(isInitial, false, resSucc);
		}
		return resSucc;
	}

	private IPredicate getOrConstructLoopPredicate(final Set<IPredicate> inputSuccs, final boolean isInitial) {
		final IPredicate resSucc = getOrConstructPredicate(inputSuccs, mLoopPU, mLoopInputPreds2ResultPreds,
				mLoopResPred2InputPreds);
		if (!mAlreadyConstrucedAutomaton.contains(resSucc)) {
			mAlreadyConstrucedAutomaton.addState(isInitial, false, resSucc);
		}
		return resSucc;
	}

	private void addNonAcceptingSuccStem(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		for (final IPredicate succCand : mInputStemPredicates) {
			final Validity validity = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (validity == Validity.VALID) {
				inputSuccs.add(succCand);
			}
		}
		if (!inputSuccs.isEmpty()) {
			final IPredicate resSucc = getOrConstructStemPredicate(inputSuccs, false);
			sch.addTransition(resPred, resHier, letter, resSucc);
		}
	}

	private void computeSuccsLoop(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		IPredicate acceptingSucc;
		if (mayEnterAcceptingFromLoop(letter)) {
			acceptingSucc = addAcceptingSuccLoop(resPred, resHier, letter, sch);
		} else {
			acceptingSucc = null;
		}
		if (acceptingSucc == null || mScroogeNondeterminismLoop) {
			addNonAcceptingSuccLoop(resPred, resHier, letter, sch);
		}
	}

	private IPredicate addAcceptingSuccLoop(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		final Validity validityDecr = sch.computeSuccWithSolver(resPred, resHier, letter, mBspm.getRankDecreaseAndBound());
		if (validityDecr != Validity.VALID) {
			return null;
		}
		final Set<IPredicate> inputSuccsWithoutAux = new HashSet<IPredicate>();
		for (final IPredicate succCand : mInputAuxFreePredicates) {
			final Validity validity = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (validity == Validity.VALID) {
				inputSuccsWithoutAux.add(succCand);
			}
		}
		final IPredicate resSucc = getOrConstructAcceptingPredicate(inputSuccsWithoutAux, false);
		sch.addTransition(resPred, resHier, letter, resSucc);
		return resSucc;
	}

	private void addNonAcceptingSuccLoop(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
			final SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		for (final IPredicate succCand : mInputLoopPredicates) {
			final Validity validity = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (validity == Validity.VALID) {
				inputSuccs.add(succCand);
			}
		}
		if (!inputSuccs.isEmpty()) {
			final IPredicate resSucc = getOrConstructLoopPredicate(inputSuccs, false);
			sch.addTransition(resPred, resHier, letter, resSucc);
		}
	}

	private IPredicate getOrConstructPredicate(final Set<IPredicate> succs, final PredicateUnifier predicateUnifier,
			final Map<Set<IPredicate>, IPredicate> inputPreds2ResultPreds,
			final HashRelation<IPredicate, IPredicate> resPred2InputPreds) {
		IPredicate resSucc = inputPreds2ResultPreds.get(succs);
		if (resSucc == null) {
			final Term conjunction = mPredicateFactory.and(succs);
			resSucc = predicateUnifier.getOrConstructPredicate(conjunction);
			assert resSucc != mIaFalseState : "false should have been handeled before";
			inputPreds2ResultPreds.put(succs, resSucc);
			for (final IPredicate succ : succs) {
				resPred2InputPreds.addPair(resSucc, succ);
			}
		}
		return resSucc;
	}

	/**
	 * Do we allow that a transition labeled with letter has the honda as
	 * target.
	 * 
	 * @param letter
	 * @return
	 */
	protected boolean mayEnterAcceptingFromLoop(final CodeBlock letter) {
		return !mHondaBouncerLoop || letter.equals(mHondaEntererLoop);
	}

	/**
	 * Do we allow that a transition labeled with letter has the honda as
	 * target.
	 * 
	 * @param letter
	 * @return
	 */
	protected boolean mayEnterAcceptingFromStem(final CodeBlock letter) {
		return !mHondaBouncerStem || letter.equals(mHondaEntererStem);
	}



}
