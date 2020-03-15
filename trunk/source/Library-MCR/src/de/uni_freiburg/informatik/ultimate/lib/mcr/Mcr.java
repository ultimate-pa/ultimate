package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
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

	private final McrTraceCheckResult<LETTER> mResult;

	public Mcr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final IRun<LETTER, ?> counterexample,
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
		// Explore all the interleavings of trace
		mResult = exploreInterleavings(counterexample);
	}

	private McrTraceCheckResult<LETTER> exploreInterleavings(final IRun<LETTER, ?> counterexample)
			throws AutomataLibraryException {
		final McrAutomatonBuilder<LETTER> automatonBuilder = constructAutomatonBuilder(counterexample);
		final INestedWordAutomaton<LETTER, ?> mhbAutomaton = automatonBuilder.buildMhbAutomaton();
		McrTraceCheckResult<LETTER> result;
		IsEmpty<LETTER, ?> isEmpty;
		IRun<LETTER, ?> currentCounterexample = counterexample;
		// TODO: Fix do-while
		do {
			result = checkCounterexample(currentCounterexample);
			if (result.isCorrect() != LBool.UNSAT) {
				return result;
			}
			// TODO: Subtract result.getAutomaton() from mhbAutomaton
			isEmpty = new IsEmpty<>(mAutomataServices, mhbAutomaton);
			currentCounterexample = isEmpty.getNestedRun();
		} while (isEmpty.checkResult(null));
		// All interleavings are infeasible
		return result;
	}

	private McrTraceCheckResult<LETTER> checkCounterexample(final IRun<LETTER, ?> counterexample)
			throws AutomataLibraryException {
		final Pair<LBool, QualifiedTracePredicates> proof =
				mProofProvider.getProof(counterexample, getPrecondition(), getPostcondition());
		final List<LETTER> trace = counterexample.getWord().asList();
		final LBool feasibility = proof.getFirst();
		if (feasibility != LBool.UNSAT) {
			// We found a feasible error trace
			return new McrTraceCheckResult<>(trace, feasibility, null, null);
		}
		final McrAutomatonBuilder<LETTER> automatonBuilder = constructAutomatonBuilder(counterexample);
		final NestedWordAutomaton<LETTER, IPredicate> interpolantAutomaton =
				automatonBuilder.buildInterpolantAutomaton(Collections.singletonList(proof.getSecond()));
		final List<IPredicate> predicates = proof.getSecond().getPredicates();
		final IPredicate[] interpolants = predicates.toArray(new IPredicate[predicates.size()]);
		return new McrTraceCheckResult<>(trace, LBool.UNSAT, interpolantAutomaton, interpolants);
	}

	private McrAutomatonBuilder<LETTER> constructAutomatonBuilder(final IRun<LETTER, ?> counterexample) {
		return new McrAutomatonBuilder<>(counterexample.getWord().asList(), mPredicateUnifier, mEmptyStackStateFactory,
				mLogger, mAlphabet, mServices, mManagedScript, mXnfConversionTechnique, mSimplificationTechnique);
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
