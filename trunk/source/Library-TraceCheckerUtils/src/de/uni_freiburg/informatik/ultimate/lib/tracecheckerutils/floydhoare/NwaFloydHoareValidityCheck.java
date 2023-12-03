package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class NwaFloydHoareValidityCheck<L extends IAction, S> extends FloydHoareValidityCheck<S> {
	private final INestedWordAutomaton<L, S> mAutomaton;

	public NwaFloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final INestedWordAutomaton<L, S> automaton,
			final IFloydHoareAnnotation<S> annotation, final boolean assertValidity,
			final MissingAnnotationBehaviour missingAnnotations, final boolean checkSafety) {
		super(services, mgdScript, hoareTripleChecker, annotation, assertValidity, missingAnnotations, checkSafety);
		mAutomaton = automaton;

		mLogger.info("Starting Floyd-Hoare check of an automaton with " + automaton.sizeInformation());
		performCheck();
	}

	public static <L extends IAction> NwaFloydHoareValidityCheck<L, IPredicate> forInterpolantAutomaton(
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final IPredicateUnifier unifier,
			final INestedWordAutomaton<L, IPredicate> automaton, final boolean assertValidity) {
		return new NwaFloydHoareValidityCheck<>(services, mgdScript, hoareTripleChecker, automaton,
				new FloydHoareForInterpolantAutomaton(unifier), assertValidity, MissingAnnotationBehaviour.THROW,
				false);
	}

	@Override
	protected Iterable<S> getInitialStates() {
		return mAutomaton.getInitialStates();
	}

	@Override
	protected boolean isPostState(final S state) {
		return mAutomaton.isFinal(state);
	}

	@Override
	protected Iterable<Pair<IInternalAction, S>> getInternalSuccessors(final S state) {
		return successors(mAutomaton.internalSuccessors(state), IInternalAction.class);
	}

	@Override
	protected Iterable<Pair<ICallAction, S>> getCallSuccessors(final S state) {
		return successors(mAutomaton.callSuccessors(state), ICallAction.class);
	}

	@Override
	protected Iterable<Triple<IReturnAction, S, S>> getReturnSuccessors(final S state) {
		final var retSuccs = mAutomaton.returnSuccessors(state);
		return () -> new TransformIterator<>(retSuccs.iterator(),
				t -> new Triple<>((IReturnAction) t.getLetter(), t.getSucc(), t.getHierPred()));
	}

	private <A> Iterable<Pair<A, S>> successors(final Iterable<? extends IOutgoingTransitionlet<L, S>> successors,
			final Class<A> clazz) {
		return () -> new TransformIterator<>(successors.iterator(),
				t -> new Pair<>(clazz.cast(t.getLetter()), t.getSucc()));
	}
}