package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class BuchiPetriNetCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNet<L, IPredicate>> {

	public BuchiPetriNetCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNet<L, IPredicate> initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
	}

	@Override
	protected boolean isAbstractionEmpty(final IPetriNet<L, IPredicate> abstraction) throws AutomataLibraryException {
		// TODO: Insert actual emptiness check (when finished)
		return false;
	}

	@Override
	protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
			final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton =
				constructInterpolantAutomaton(lassoCheck, new VpAlphabet<>(abstraction.getAlphabet()));
		// TODO: Insert actual difference (when finished)
		return null;
	}

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate>
			constructInterpolantAutomaton(final LassoCheck<L> lassoCheck, final VpAlphabet<L> alphabet) {
		// TODO: This is mostly copied code from RefineBuchi. Can we merge this?
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();

		final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
		assert !bspm.getStemPrecondition().getFormula().toString().equals("false");
		assert !bspm.getHondaPredicate().getFormula().toString().equals("false");
		assert !bspm.getRankEqAndSi().getFormula().toString().equals("false");
		final PredicateUnifier pu = new PredicateUnifier(mLogger, mServices, mCsToolkitWithRankVars.getManagedScript(),
				mPredicateFactory, mCsToolkitWithRankVars.getSymbolTable(), SIMPLIFICATION_TECHNIQUE,
				XNF_CONVERSION_TECHNIQUE, bspm.getStemPrecondition(), bspm.getHondaPredicate(), bspm.getRankEqAndSi(),
				bspm.getStemPostcondition(), bspm.getRankDecreaseAndBound(), bspm.getSiConjunction());
		IPredicate[] stemInterpolants;
		InterpolatingTraceCheck<L> traceCheck;
		if (BuchiAutomizerUtils.isEmptyStem(mCounterexample)) {
			stemInterpolants = null;
		} else {

			traceCheck = constructTraceCheck(bspm.getStemPrecondition(), bspm.getStemPostcondition(), stem, pu,
					mInterpolation);
			final LBool stemCheck = traceCheck.isCorrect();
			if (stemCheck != LBool.UNSAT) {
				throw new AssertionError("incorrect predicates - stem");
			}
			stemInterpolants = traceCheck.getInterpolants();
		}

		traceCheck = constructTraceCheck(bspm.getRankEqAndSi(), bspm.getHondaPredicate(), loop, pu, mInterpolation);
		final LBool loopCheck = traceCheck.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck != LBool.UNSAT) {
			throw new AssertionError("incorrect predicates - loop");
		}
		loopInterpolants = traceCheck.getInterpolants();

		final NestedWordAutomaton<L, IPredicate> interpolAutomaton = BuchiAutomizerUtils
				.constructBuchiInterpolantAutomaton(bspm.getStemPrecondition(), stem, stemInterpolants,
						bspm.getHondaPredicate(), loop, loopInterpolants, alphabet, mServices, mDefaultStateFactory);
		final IHoareTripleChecker ehtc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
		final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
		bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert new InductivityCheck<>(mServices, interpolAutomaton, false, true, bhtc).getResult();
		// TOOD: Enhance interpolAutomaton first (using which technique?)
		return interpolAutomaton;
	}

	private InterpolatingTraceCheck<L> constructTraceCheck(final IPredicate precond, final IPredicate postcond,
			final NestedWord<L> word, final PredicateUnifier pu, final InterpolationTechnique interpolation) {
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			return new InterpolatingTraceCheckCraig<>(precond, postcond, new TreeMap<Integer, IPredicate>(), word, null,
					mServices, mCsToolkitWithRankVars, mPredicateFactory, pu, AssertCodeBlockOrder.NOT_INCREMENTALLY,
					false, false, interpolation, true, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE);
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect: {
			return new TraceCheckSpWp<>(precond, postcond, new TreeMap<Integer, IPredicate>(), word,
					mCsToolkitWithRankVars, AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true,
					mServices, false, mPredicateFactory, pu, interpolation, mCsToolkitWithRankVars.getManagedScript(),
					XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE, null, false);
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
	}

	@Override
	protected IPetriNet<L, IPredicate> refineFinite(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataOperationCanceledException {
		// TODO: Insert actual difference (when finished). Is there a special case for finite automata?
		return null;
	}

}
