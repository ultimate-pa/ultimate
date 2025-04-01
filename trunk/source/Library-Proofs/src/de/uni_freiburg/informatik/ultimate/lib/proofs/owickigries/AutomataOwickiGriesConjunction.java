package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomatonToOG;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireComputation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class AutomataOwickiGriesConjunction<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private BranchingProcess<L, P> mRefinedUnfolding;

	private final Statistics mStatistics;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private final List<INestedWordAutomaton<L, IPredicate>> mProofs = new ArrayList<>();
	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;

	public AutomataOwickiGriesConjunction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable());
	}

	public AutomataOwickiGriesConjunction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);
		mProofs.add(interpolantAutomaton);
	}

	@Override
	public boolean isReadyToComputeProof() {
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		mStatistics.startOwickiGriesComputation();
		final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
				mProgram.getPlaces(), mDiff2OriginalTransition);
		final var annotations = getOGAnnotations(possibleInterferences);
		mOwickiGries = annotations.stream().reduce(null, (a, b) -> new OwickiGriesConjunction<L, P>(mServices,
				mMgdScript, mProgram, mSymbolTable, mProcedures, a, b, possibleInterferences).getAnnotation());
		mStatistics.stopOwickiGriesComputation();
		return mOwickiGries;
	}

	private Set<OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>>>
			getOGAnnotations(final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		final var annotations = new HashSet<OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>>>();
		for (final INestedWordAutomaton<L, IPredicate> proof : mProofs) {
			final var empireAutomaton = new EmpireAutomaton<>(mProgram, proof, mServices);
			final var empireToOG = getOwickiGriesAnnotation(empireAutomaton, possibleInterferences);
			mLogger.info(empireToOG.getAnnotation());
			assert checkOwickiGriesValidity(empireToOG.getAnnotation()) : "Owicki Gries annotation is invalid";
			annotations.add(empireToOG.getAnnotation());
		}
		return annotations;
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		mStatistics.startOwickiGriesValidity();
		try {
			final var validity =
					new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mProgram, mModifiableGlobals, annotation)
							.isValid();
			assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Owicki-Gries annotation");
			}
			return validity != Validity.INVALID;
		} finally {
			mStatistics.stopOwickiGriesValidity();
		}
	}

	@Override
	public void finalize(final IPetriNet<L, P> refinedNet, final BranchingProcess<L, P> refinedNetUnfolding) {
		mRefinedUnfolding = refinedNetUnfolding;
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	private EmpireAutomatonToOG<L, P> getOwickiGriesAnnotation(final EmpireAutomaton<L, P> empireAutomaton,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		return new EmpireAutomatonToOG<>(mServices, mMgdScript, mProgram, mSymbolTable, mProcedures, empireAutomaton,
				possibleInterferences);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		public Statistics(final ILogger logger) {
			super(logger, EmpireComputation.class, EmpireToOwickiGries.class);
		}

		public void reportEmpire(final IStatisticsDataProvider statistics) {
			reportEmpireStatistics(statistics, null);
		}
	}
}
