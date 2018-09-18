/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.UnfoldingOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IFinitePrefix2PetriNetStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

public class CegarLoopJulian<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {

	private BranchingProcess<LETTER, IPredicate> mUnfolding;
	public int mCoRelationQueries = 0;
	public int mBiggestAbstractionTransitions;
	/**
	 * Do not enhance the interpolant automaton into a total automaton but construct
	 * the enhancement only on-demand and add only transitions that will be needed
	 * for the difference.
	 */
	private final boolean mEnhanceInterpolantAutomatonOnDemand = true;
	/**
	 * Remove unreachable nodes of mAbstraction in each iteration.
	 */
	private final boolean mRemoveUnreachable = true;

	public CegarLoopJulian(final DebugIdentifier name, final BoogieIcfgContainer rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TraceAbstractionBenchmarks timingStatistics, final TAPreferences taPrefs,
			final Collection<BoogieIcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				InterpolationTechnique.Craig_TreeInterpolation, false, services, storage);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		final TaConcurContentFactory contentFactory = new TaConcurContentFactory(this, super.mCsToolkit,
				mPredicateFactory, super.mPref.computeHoareAnnotation(), mPref.computeHoareAnnotation(), false);
		final boolean useTildeInitWorkaround = mIcfg.getProcedureEntryNodes().containsKey("~init");
		if (useTildeInitWorkaround) {
		mLogger.warn("Program has a \"~init\" procedure. Ultimate will use the old wokaround for concurrent programs");
		final Cfg2NetJulian<LETTER> cFG2Automaton = new Cfg2NetJulian<>(mIcfg, mPredicateFactoryResultChecking,
				mCsToolkit, mPredicateFactory, mServices, mXnfConversionTechnique, mSimplificationTechnique);
		mAbstraction = cFG2Automaton.getResult();
		} else {
			final IcfgLocation initialNode = mIcfg.getProcedureEntryNodes().get(TraceAbstractionStarter.ULTIMATE_START);
			if (initialNode == null) {
				throw new UnsupportedOperationException("Program must have " + TraceAbstractionStarter.ULTIMATE_START
						+ " procedure (this is the procedure where all executions start)");
			}
			mAbstraction = CFG2NestedWordAutomaton.constructPetriNetWithSPredicates(mServices, mIcfg,
					mStateFactoryForRefinement, mErrorLocs, false, mPredicateFactory);
		}

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = "Abstraction" + mIteration;
			writeAutomatonToFile(mAbstraction, filename);
		}
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final BoundedPetriNet<LETTER, IPredicate> abstraction = (BoundedPetriNet<LETTER, IPredicate>) mAbstraction;
		final String orderString = mPref.order();
		final boolean cutOffSameTrans = mPref.cutOffRequiresSameTransition();
		UnfoldingOrder ord;
		if (orderString.equals(UnfoldingOrder.KMM.getDescription())) {
			ord = UnfoldingOrder.KMM;
		} else if (orderString.equals(UnfoldingOrder.ERV.getDescription())) {
			ord = UnfoldingOrder.ERV;
		} else if (orderString.equals(UnfoldingOrder.ERV_MARK.getDescription())) {
			ord = UnfoldingOrder.ERV_MARK;
		} else {
			throw new IllegalArgumentException("Unknown order " + orderString);
		}

		final PetriNetUnfolder<LETTER, IPredicate> unf = new PetriNetUnfolder<>(new AutomataLibraryServices(mServices),
				abstraction, ord, cutOffSameTrans, !mPref.unfoldingToNet());
		mUnfolding = unf.getFinitePrefix();
		mCoRelationQueries += mUnfolding.getCoRelation().getQueryCounter();

		mCounterexample = unf.getAcceptingRun();
		if (mCounterexample == null) {
			return true;
		}
		if (mPref.dumpAutomata()) {
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DUMP_TIME);
			mDumper.dumpNestedRun(mCounterexample);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
		}
		return false;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		BoundedPetriNet<LETTER, IPredicate> abstraction = (BoundedPetriNet<LETTER, IPredicate>) mAbstraction;
		if (mPref.unfoldingToNet()) {
			// TODO: Find/implement appropriate stateFactory.
			final IFinitePrefix2PetriNetStateFactory<IPredicate> stateFactory = null;
			abstraction = new FinitePrefix2PetriNet<>(new AutomataLibraryServices(mServices), stateFactory, mUnfolding)
					.getResult();
		}

		// Determinize the interpolant automaton
		final INestedWordAutomaton<LETTER, IPredicate> dia = enhanceAnddeterminizeInterpolantAutomaton(mInterpolAutomaton);

		// Complement the interpolant automaton
		final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> nia =
				new ComplementDD<>(new AutomataLibraryServices(mServices), mPredicateFactoryInterpolantAutomata, dia)
						.getResult();
		// TODO 2018-08-11 Matthias: Complement not needed since we compute difference.
		// Furthermore there is a problem because we would have to concatenate operand
		// with some ∑^* automaton first and we do not yet have an implementation for
		// that.
//		assert !accepts(mServices, nia, mCounterexample.getWord(), false) : "Complementation broken!";
//		mLogger.info("Complemented interpolant automaton has " + nia.size() + " states");

		if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			mArtifactAutomaton = nia;
		}
		mAbstraction = new Difference<>(new AutomataLibraryServices(mServices), mPredicateFactoryInterpolantAutomata,
				abstraction, dia).getResult();

		if (mRemoveUnreachable) {
			mAbstraction = new de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveUnreachable(
					new AutomataLibraryServices(mServices), (BoundedPetriNet) mAbstraction).getResult();
		}

		if (mPref.dumpAutomata()) {
			// TODO Matthias: Iteration should probably added to TaskIdentifier
			final String filename = mTaskIdentifier + ("_Iteration" + mIteration) + ("_AbstractionAfterDifference");
			super.writeAutomatonToFile(mAbstraction, filename);
		}

		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);
		// if (mBiggestAbstractionSize < mAbstraction.size()){
		// mBiggestAbstractionSize = mAbstraction.size();
		// mBiggestAbstractionTransitions =
		// abstraction.getTransitions().size();
		// mBiggestAbstractionIteration = mIteration;
		// }

		assert !acceptsPetriViaFA(mServices, mAbstraction, mCounterexample.getWord()) : "Intersection broken!";

		// int[] statistic = mAbstraction.transitions();
		// s_Logger.debug("Abstraction has " +
		// mAbstraction.getAllStates().size() + "states, " +
		// statistic[0] + " internal transitions " + statistic[1] +
		// "call transitions " + statistic[2]+ " return transitions ");

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = "Abstraction" + mIteration;
			writeAutomatonToFile(mAbstraction, filename);
		}
		return true;
	}

	protected INestedWordAutomaton<LETTER, IPredicate>
			enhanceAnddeterminizeInterpolantAutomaton(final INestedWordAutomaton<LETTER, IPredicate> interpolAutomaton)
					throws AutomataOperationCanceledException {
		mLogger.debug("Start determinization");
		INestedWordAutomaton<LETTER, IPredicate> dia;
		switch (mPref.interpolantAutomatonEnhancement()) {
		case NONE:
			final PowersetDeterminizer<LETTER, IPredicate> psd =
					new PowersetDeterminizer<>(interpolAutomaton, true, mPredicateFactoryInterpolantAutomata);
			final DeterminizeDD<LETTER, IPredicate> dabps =
					new DeterminizeDD<>(new AutomataLibraryServices(mServices), mPredicateFactoryInterpolantAutomata, interpolAutomaton, psd);
			dia = dabps.getResult();
			break;
		case PREDICATE_ABSTRACTION:
			final IHoareTripleChecker htc = new IncrementalHoareTripleChecker(super.mCsToolkit, false);
			final DeterministicInterpolantAutomaton<LETTER> raw =
					new DeterministicInterpolantAutomaton<>(mServices, mCsToolkit, htc, interpolAutomaton,
							mTraceCheckAndRefinementEngine.getPredicateUnifier(), false, false);
			if (mEnhanceInterpolantAutomatonOnDemand) {
				new DifferencePairwiseOnDemand(new AutomataLibraryServices(mServices) , mPredicateFactoryInterpolantAutomata, (IPetriNet) mAbstraction, raw);
				raw.switchToReadonlyMode();
			}
			dia = new RemoveUnreachable(new AutomataLibraryServices(mServices), raw).getResult();
			final double dfaTransitionDensity = new Analyze<>(new AutomataLibraryServices(mServices), dia, false).getTransitionDensity(SymbolType.INTERNAL);
			mLogger.info("DFA transition density " + dfaTransitionDensity);
			if (mPref.dumpAutomata()) {
				// TODO Matthias: Iteration should probably added to TaskIdentifier
				final String filename = mTaskIdentifier + ("_Iteration" + mIteration) + ("_EagerFloydHoareAutomaton");
				super.writeAutomatonToFile(dia, filename);
			}
			break;
		default:
			throw new UnsupportedOperationException();
		}

		if (mComputeHoareAnnotation) {
			assert new InductivityCheck<>(mServices, dia, false, true,
					new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult() : "Not inductive";
		}
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomatonDeterminized_Iteration" + mIteration;
			writeAutomatonToFile(dia, filename);
		}
		assert accepts(mServices, dia,
				mCounterexample.getWord(), true) : "Counterexample not accepted by determinized interpolant automaton: "
						+ mCounterexample.getWord();
		mLogger.debug("Sucessfully determinized");
		return dia;
	}

	@Override
	protected void computeCFGHoareAnnotation() {
		throw new UnsupportedOperationException();
	}

	private boolean acceptsPetriViaFA(final IUltimateServiceProvider services,
			final IAutomaton<LETTER, IPredicate> automaton, final Word<LETTER> word)
			throws AutomataOperationCanceledException {
		final NestedWord<LETTER> nw = NestedWord.nestedWord(word);
		final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> petriNetAsFA =
				new PetriNet2FiniteAutomaton<>(new AutomataLibraryServices(services), mPredicateFactoryResultChecking,
						(IPetriNet<LETTER, IPredicate>) automaton).getResult();
		return super.accepts(services, petriNetAsFA, nw, false);

	}

	@Override
	public IPreconditionProvider getPreconditionProvider() {

		final IPreconditionProvider result = new IPreconditionProvider() {

			@Override
			public IPredicate constructPrecondition(final PredicateUnifier predicateUnifier) {
				final ConcurrencyInformation ci = mIcfg.getCfgSmtToolkit().getConcurrencyInformation();
				if (ci == null) {
					return predicateUnifier.getTruePredicate();
				} else {
					final Set<BoogieNonOldVar> threadInUseVars = ci.getThreadInUseVars().entrySet().stream()
							.map(Entry::getValue).collect(Collectors.toSet());
					final List<Term> negated = threadInUseVars.stream().map(x -> SmtUtils
							.not(mIcfg.getCfgSmtToolkit().getManagedScript().getScript(), x.getTermVariable()))
							.collect(Collectors.toList());
					final Term conjunction = SmtUtils.and(mIcfg.getCfgSmtToolkit().getManagedScript().getScript(),
							negated);
					return predicateUnifier.getOrConstructPredicate(conjunction);
				}
			}
		};
		return result;
	}



}
