package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class EmpireAutomataConstruction<L extends IAction, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final BasicPredicateFactory mFactory;

	private final IUnionStateFactory<IPredicate> mUnionFactory;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProofProduct;

	public EmpireAutomataConstruction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable,
			final ModifiableGlobalsTable modifiableGlobals, final PredicateFactory factory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mModifiableGlobals = modifiableGlobals;
		mFactory = factory;
		mUnionFactory = new UnionFactory(factory);
	}

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

	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	public EmpireAutomaton<L, P> getOrComputeAutomaton() {
		final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
		final var htc = new MonolithicHoareTripleChecker(mMgdScript, mModifiableGlobals);

		final var automaton = new EmpireAutomaton<>(mProgram, mProofProduct, mServices);
		mLogger.debug("Constructed Empire Automaton");

		assert checkAutomatonValidity(automaton) : "Empire automaton is invalid";

		return automaton;
	}

	private boolean checkAutomatonValidity(final EmpireAutomaton<L, P> automaton) {
		try {
			final var checker = new EmpireAutomatonValidityCheck<>(mServices, mMgdScript, mFactory, mProgram,
					mModifiableGlobals, automaton);
			return checker.getValidity() != Validity.INVALID;
		} finally {
		}
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
