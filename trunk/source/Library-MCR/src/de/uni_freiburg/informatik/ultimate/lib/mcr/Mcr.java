package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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
	private final IMcrResultProvider<LETTER> mResultProvider;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;

	private final McrTraceCheckResult<LETTER> mResult;

	public Mcr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final List<LETTER> trace,
			final Set<LETTER> alphabet, final IMcrResultProvider<LETTER> resultProvider)
			throws AutomataLibraryException {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = prefs.getUltimateServices();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mAlphabet = alphabet;
		mManagedScript = prefs.getCfgSmtToolkit().getManagedScript();
		mXnfConversionTechnique = prefs.getXnfConversionTechnique();
		mSimplificationTechnique = prefs.getSimplificationTechnique();
		mEmptyStackStateFactory = emptyStackStateFactory;
		mResultProvider = resultProvider;
		// Explore all the interleavings of trace
		mResult = exploreInterleavings(trace);
	}

	private McrTraceCheckResult<LETTER> exploreInterleavings(final List<LETTER> initialTrace)
			throws AutomataLibraryException {
		final McrAutomatonBuilder<LETTER> automatonBuilder =
				new McrAutomatonBuilder<>(initialTrace, mPredicateUnifier, mEmptyStackStateFactory, mLogger, mAlphabet,
						mServices, mManagedScript, mXnfConversionTechnique, mSimplificationTechnique);
		final StringFactory factory = new StringFactory();
		final List<INestedWordAutomaton<LETTER, IPredicate>> automata = new ArrayList<>();
		INestedWordAutomaton<LETTER, String> mhbAutomaton = automatonBuilder.buildMhbAutomaton();
		NestedRun<LETTER, ?> run = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		int iteration = 0;
		McrTraceCheckResult<LETTER> result = null;
		while (run != null) {
			mLogger.info("---- MCR iteration " + iteration++ + " ----");
			result = mResultProvider.getResult(run, getPrecondition(), getPostcondition());
			final List<LETTER> trace = run.getWord().asList();
			if (result.isCorrect() != LBool.UNSAT) {
				// We found a feasible error trace
				return result;
			}
			final INestedWordAutomaton<LETTER, IPredicate> automaton =
					automatonBuilder.buildInterpolantAutomaton(trace, result.getQualifiedTracePredicates());
			automata.add(automaton);
			final INestedWordAutomaton<LETTER, String> convertedAutomaton = convertInterpolantAutomaton(automaton);
			mhbAutomaton = new Difference<>(mAutomataServices, factory, mhbAutomaton, convertedAutomaton).getResult();
			run = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		}
		// All interleavings are infeasible, therefore create an interpolant automaton
		result.setAutomaton(unionAutomata(automata));
		return result;
	}

	private INestedWordAutomaton<LETTER, String>
			convertInterpolantAutomaton(final INestedWordAutomaton<LETTER, IPredicate> automaton) {
		// TODO Auto-generated method stub
		return null;
	}

	private NestedWordAutomaton<LETTER, IPredicate>
			unionAutomata(final List<INestedWordAutomaton<LETTER, IPredicate>> automata) {
		// TODO Auto-generated method stub
		return null;
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
		switch (isCorrect()) {
		case SAT:
			return new InterpolantComputationStatus();
		case UNKNOWN:
			return new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		default:
			throw new UnsupportedOperationException();
		}
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
		return mResult.providesExecution();
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		return mResult.getExecution();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mResult.getStatistics();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null, ExceptionHandlingCategory.KNOWN_THROW);
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return true;
	}

	public interface IMcrResultProvider<LETTER extends IIcfgTransition<?>> {
		McrTraceCheckResult<LETTER> getResult(IRun<LETTER, ?> counterexample, IPredicate precondition,
				IPredicate postcondition);
	}
}
