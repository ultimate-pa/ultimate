package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPetriNetProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.PetriOwickiGriesValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class EmpireAutomataConstruction<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final BasicPredicateFactory mFactory;
	private BranchingProcess<L, P> mRefinedUnfolding;

	private final IUnionStateFactory<IPredicate> mUnionFactory;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProofProduct;
	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;

	public EmpireAutomataConstruction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final PredicateFactory factory) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable(), factory);
	}

	public EmpireAutomataConstruction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final PredicateFactory factory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mFactory = factory;
		mUnionFactory = new UnionFactory(factory);
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);
		if (mProofProduct == null) {
			mProofProduct = interpolantAutomaton;
		} else {
			final var initialTrueState1 =
					DataStructureUtils.getOneAndOnly(mProofProduct.getInitialStates(), "initial state");
			final var totalizedProduct = new TotalizeNwa<>(mProofProduct, initialTrueState1, false);

			final var initialTrueState2 =
					DataStructureUtils.getOneAndOnly(interpolantAutomaton.getInitialStates(), "initial state");
			final var totalizedProof = new TotalizeNwa<>(interpolantAutomaton, initialTrueState2, false);

			try {
				mProofProduct = new UnionNwa<>(totalizedProduct, totalizedProof, mUnionFactory, false);
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Override
	public boolean isReadyToComputeProof() {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		final var automaton = new EmpireAutomaton<>(mProgram, mProofProduct, mServices);
		mLogger.debug("Constructed Empire Automaton");

		assert checkAutomatonValidity(automaton) : "Empire automaton is invalid";

		mOwickiGries = getOwickiGriesAnnotation(automaton);
		mLogger.debug("Computed Owicki-Gries annotation:\n%s", mOwickiGries);

		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";

		return mOwickiGries;
	}

	private boolean checkAutomatonValidity(final EmpireAutomaton<L, P> automaton) {
		final var checker = new EmpireAutomatonValidityCheck<>(mServices, mMgdScript, mFactory, mProgram,
				mModifiableGlobals, automaton);
		return checker.getValidity() != Validity.INVALID;
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		final var validity =
				new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mProgram, mModifiableGlobals, annotation)
						.isValid();
		assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
		if (validity == Validity.UNKNOWN) {
			mLogger.warn("Could not prove validity of Owicki-Gries annotation");
		}
		return validity != Validity.INVALID;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void finalize(final IPetriNet<L, P> refinedNet, final BranchingProcess<L, P> refinedNetUnfolding) {
		mRefinedUnfolding = refinedNetUnfolding;
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>>
			getOwickiGriesAnnotation(final EmpireAutomaton<L, P> empireAutomaton) {
		final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
				mProgram.getPlaces(), mDiff2OriginalTransition);
		final EmpireAutomatonToOG<L, P> empireToOwickiGries = new EmpireAutomatonToOG<>(mServices, mMgdScript, mProgram,
				mSymbolTable, mProcedures, empireAutomaton, possibleInterferences);
		return empireToOwickiGries.getAnnotation();
	}

	private static final class UnionFactory implements IUnionStateFactory<IPredicate> {
		private final PredicateFactory mPredicateFactory;
		private final IPredicate mEmptyStack;

		public UnionFactory(final PredicateFactory predicateFactory) {
			mPredicateFactory = predicateFactory;
			mEmptyStack = predicateFactory.newEmptyStackPredicate();
		}

		@Override
		public IPredicate createEmptyStackState() {
			return mEmptyStack;
		}

		@Override
		public IPredicate createSinkStateContent() {
			return mPredicateFactory.and();
		}

		@Override
		public IPredicate union(final IPredicate state1, final IPredicate state2) {
			return mPredicateFactory.and(state1, state2);
		}
	}
}
