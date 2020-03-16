package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class Mcr<LETTER extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<LETTER> {
	private final ILogger mLogger;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;
	private final ManagedScript mManagedScript;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private final Set<LETTER> mAlphabet;
	private final IProofProvider<LETTER> mProofProvider;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private final List<LETTER> mInitialTrace;

	private final McrTraceCheckResult<LETTER> mResult;

	public Mcr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final List<LETTER> trace,
			final Set<LETTER> alphabet, final IProofProvider<LETTER> proofProvider) throws AutomataLibraryException {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = prefs.getUltimateServices();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mAlphabet = alphabet;
		mManagedScript = prefs.getCfgSmtToolkit().getManagedScript();
		mXnfConversionTechnique = prefs.getXnfConversionTechnique();
		mSimplificationTechnique = prefs.getSimplificationTechnique();
		mEmptyStackStateFactory = emptyStackStateFactory;
		mProofProvider = proofProvider;
		mInitialTrace = trace;
		// Explore all the interleavings of trace
		mResult = exploreInterleavings(trace);
	}

	private McrTraceCheckResult<LETTER> exploreInterleavings(final List<LETTER> initialTrace)
			throws AutomataLibraryException {
		final McrAutomatonBuilder<LETTER> automatonBuilder =
				new McrAutomatonBuilder<>(initialTrace, mPredicateUnifier, mEmptyStackStateFactory, mLogger, mAlphabet,
						mServices, mManagedScript, mXnfConversionTechnique, mSimplificationTechnique);
		final StringFactory factory = new StringFactory();
		final List<INestedWordAutomaton<Integer, String>> automata = new ArrayList<>();
		final List<QualifiedTracePredicates> tracePredicates = new ArrayList<>();
		final List<List<Integer>> intTraces = new ArrayList<>();
		INestedWordAutomaton<Integer, String> mhbAutomaton = automatonBuilder.buildMhbAutomaton();
		NestedRun<Integer, ?> run = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		List<LETTER> currentTrace = null;
		int iteration = 0;
		while (run != null) {
			mLogger.info("---- MCR iteration " + iteration++ + " ----");
			final NestedRun<LETTER, ?> counterexample = convertRun(run);
			final Pair<LBool, QualifiedTracePredicates> proof =
					mProofProvider.getProof(counterexample, getPrecondition(), getPostcondition());
			currentTrace = counterexample.getWord().asList();
			final LBool feasibility = proof.getFirst();
			if (feasibility != LBool.UNSAT) {
				// We found a feasible error trace
				return new McrTraceCheckResult<>(currentTrace, feasibility, null, null);
			}
			// TODO: Use interpolant automata (from settings) here?
			final INestedWordAutomaton<Integer, String> mcrAutomaton = automatonBuilder.buildMcrAutomaton(currentTrace);
			automata.add(mcrAutomaton);
			tracePredicates.add(proof.getSecond());
			intTraces.add(run.getWord().asList());
			mhbAutomaton = new Difference<>(mAutomataServices, factory, mhbAutomaton, mcrAutomaton).getResult();
			run = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		}
		// All interleavings are infeasible
		final List<IPredicate> lastPredicates =
				tracePredicates.get(tracePredicates.size() - 1).getTracePredicates().getPredicates();
		final IPredicate[] interpolants = lastPredicates.toArray(new IPredicate[lastPredicates.size()]);
		final NestedWordAutomaton<LETTER, IPredicate> interpolantAutomaton =
				automatonBuilder.buildInterpolantAutomaton(automata, intTraces, tracePredicates);
		return new McrTraceCheckResult<>(currentTrace, LBool.UNSAT, interpolantAutomaton, interpolants);
	}

	@SuppressWarnings("unchecked")
	private <STATE> NestedRun<LETTER, STATE> convertRun(final NestedRun<Integer, STATE> intRun) {
		final LETTER[] symbols = (LETTER[]) intRun.getWord().asList().stream().map(mInitialTrace::get)
				.toArray(IIcfgTransition<?>[]::new);
		return new NestedRun<>(NestedWord.nestedWord(new Word<>(symbols)), intRun.getStateSequence());
	}

	public NestedWordAutomaton<LETTER, IPredicate> getAutomaton() {
		return mResult.getAutomaton();
	}

	@Override
	public List<LETTER> getTrace() {
		return mResult.getTrace();
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mResult.getInterpolants();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// TODO: Adapt later; for now, automata are created by MCR so it does not really matter
		return false;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		// TODO: Only a workaround, use from RefinementEngine
		return new InterpolantComputationStatus();
	}

	@Override
	public LBool isCorrect() {
		return mResult.isCorrect();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredicateUnifier.getTruePredicate();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredicateUnifier.getFalsePredicate();
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return isCorrect() != LBool.SAT;
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return true;
	}

	public interface IProofProvider<LETTER extends IIcfgTransition<?>> {
		Pair<LBool, QualifiedTracePredicates> getProof(IRun<LETTER, ?> counterexample, IPredicate precondition,
				IPredicate postcondition);
	}
}
