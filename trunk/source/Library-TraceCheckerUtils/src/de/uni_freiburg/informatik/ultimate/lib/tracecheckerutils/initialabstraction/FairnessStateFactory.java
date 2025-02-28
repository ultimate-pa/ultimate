package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.IFairnessStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.ProductState;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class FairnessStateFactory<L extends IIcfgTransition<?>, S>
		implements IFairnessStateFactory<IPredicate, ProductState<S>, L, Set<L>> {
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProgramAutomaton;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final Map<L, Term> mNegatedGuardCache = new HashMap<>();
	private final Map<Pair<L, Set<L>>, L> mCombinedGuardCache = new HashMap<>();
	private final IIcfgSymbolTable mSymbolTable;
	private final ILogger mLogger;

	public FairnessStateFactory(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> programAutomaton,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable,
			final ILogger logger) {
		mProgramAutomaton = programAutomaton;
		mServices = services;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mLogger = logger;
	}

	@Override
	public IPredicate combineStates(final IPredicate state, final ProductState<S> state2) {
		return new ProductPredicate<>((IMLPredicate) state, state2);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Pair<IPredicate, ProductState<S>> getOriginalStates(final IPredicate combinedState) {
		return new Pair<>(((ProductPredicate<S>) combinedState).getUnderlying(),
				((ProductPredicate<S>) combinedState).getAnnotation());
	}

	private Term computeNegatedGuard(final L letter) {
		return mNegatedGuardCache.computeIfAbsent(letter, x -> SmtUtils.not(mMgdScript.getScript(),
				TransFormulaUtils.computeGuardTerm(mServices, mMgdScript, x.getTransformula(), true)));
	}

	private L combineGuards(final L letter, final Set<L> guardInCurrentState) {
		final Term negatedGuards = SmtUtils.and(mMgdScript.getScript(),
				guardInCurrentState.stream().map(this::computeNegatedGuard).toList());
		if (SmtUtils.isTrueLiteral(negatedGuards)) {
			return letter;
		}
		final UnmodifiableTransFormula guardTf = TransFormulaBuilder.constructTransFormulaFromTerm(negatedGuards,
				Arrays.stream(negatedGuards.getFreeVars()).map(mSymbolTable::getProgramVar).collect(Collectors.toSet()),
				mMgdScript);
		// TODO: This cast is really ugly and does only work for IcfgEdge. Is there a better way?
		if (guardTf.isInfeasible() == Infeasibility.INFEASIBLE) {
			return (L) new WrappedIcfgInternalEdge((IcfgEdge) letter, guardTf);
		}
		// TODO: Is this the best way to create a transformula for the guard first and use sequential composition
		// then? Or would it be more efficient to use the old transformula as a basis and just add a conjunction for the
		// guard (incl. necessary variables)?
		final UnmodifiableTransFormula resultTf =
				TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, true, false, false,
						SimplificationTechnique.POLY_PAC, List.of(guardTf, letter.getTransformula()));
		return (L) new WrappedIcfgInternalEdge((IcfgEdge) letter, resultTf);
	}

	@Override
	public L combineGuard(final L letter, final Set<L> guard, final Set<L> enabledAction) {
		return mCombinedGuardCache.computeIfAbsent(
				new Pair<>(letter, DataStructureUtils.intersection(guard, enabledAction)),
				x -> combineGuards(x.getFirst(), x.getSecond()));
	}

	@Override
	public boolean isInfeasible(final L letter) {
		return letter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE;
	}

	@SuppressWarnings("unchecked")
	@Override
	public Set<L> getEnabledActions(final IPredicate state) {
		return StreamSupport.stream(
				mProgramAutomaton.internalSuccessors(((ProductPredicate<S>) state).getUnderlying()).spliterator(),
				false).map(x -> x.getLetter()).collect(Collectors.toSet());
	}

	private static final class ProductPredicate<S> extends AnnotatedPredicate<IMLPredicate, ProductState<S>>
			implements IMLPredicate {
		protected ProductPredicate(final IMLPredicate underlying, final ProductState<S> annotation) {
			super(underlying, annotation);
		}

		public ProductState<S> getAnnotation() {
			return mAnnotation;
		}

		@Override
		public IcfgLocation[] getProgramPoints() {
			return mUnderlying.getProgramPoints();
		}
	}

	private static final class WrappedIcfgInternalEdge extends IcfgEdge implements IInternalAction {
		private static final long serialVersionUID = -8992078905231068907L;

		private final UnmodifiableTransFormula mTransformula;

		protected WrappedIcfgInternalEdge(final IcfgEdge base, final UnmodifiableTransFormula transformula) {
			super(base.getSource(), base.getTarget(), base.getPayload());
			mTransformula = transformula;
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return mTransformula;
		}
	}
}
