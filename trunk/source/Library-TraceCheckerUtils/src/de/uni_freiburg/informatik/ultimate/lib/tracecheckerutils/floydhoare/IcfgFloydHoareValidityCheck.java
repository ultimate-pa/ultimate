package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class IcfgFloydHoareValidityCheck<LOC extends IcfgLocation> extends FloydHoareValidityCheck<LOC> {
	private final IIcfg<LOC> mIcfg;
	private final Set<LOC> mErrorLocs;

	public IcfgFloydHoareValidityCheck(final IUltimateServiceProvider services, final IIcfg<LOC> icfg,
			final boolean assertValidity) {
		this(services, icfg, new IcfgHoareAnnotation<>(), assertValidity, MissingAnnotationBehaviour.IGNORE, false);
	}

	public IcfgFloydHoareValidityCheck(final IUltimateServiceProvider services, final IIcfg<LOC> icfg,
			final IFloydHoareAnnotation<LOC> annotation, final boolean assertValidity,
			final MissingAnnotationBehaviour missingAnnotations, final boolean checkSafety) {
		this(services, new MonolithicHoareTripleChecker(icfg.getCfgSmtToolkit()), icfg, annotation, assertValidity,
				missingAnnotations, checkSafety);
	}

	public IcfgFloydHoareValidityCheck(final IUltimateServiceProvider services,
			final IHoareTripleChecker hoareTripleChecker, final IIcfg<LOC> icfg,
			final IFloydHoareAnnotation<LOC> annotation, final boolean assertValidity,
			final MissingAnnotationBehaviour missingAnnotations, final boolean checkSafety) {
		this(services, icfg.getCfgSmtToolkit().getManagedScript(), hoareTripleChecker, icfg, annotation, assertValidity,
				missingAnnotations, checkSafety);
	}

	public IcfgFloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final IIcfg<LOC> icfg,
			final IFloydHoareAnnotation<LOC> annotation, final boolean assertValidity,
			final MissingAnnotationBehaviour missingAnnotations, final boolean checkSafety) {
		super(services, mgdScript, hoareTripleChecker, annotation, assertValidity, missingAnnotations, checkSafety);
		mIcfg = icfg;
		mErrorLocs = icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toSet());

		if (icfg.getInitialNodes().isEmpty()) {
			mLogger.warn("There was no procedure with an implementation");
		}

		performCheck();
	}

	@Override
	protected Iterable<LOC> getInitialStates() {
		return mIcfg.getInitialNodes();
	}

	@Override
	protected boolean isPostState(final LOC state) {
		return mErrorLocs.contains(state);
	}

	@Override
	protected Iterable<Pair<IInternalAction, LOC>> getInternalSuccessors(final LOC state) {
		return getSuccessors(state, IInternalAction.class);
	}

	@Override
	protected Iterable<Pair<ICallAction, LOC>> getCallSuccessors(final LOC state) {
		return getSuccessors(state, ICallAction.class);
	}

	@Override
	protected Iterable<Triple<IReturnAction, LOC, LOC>> getReturnSuccessors(final LOC state) {
		return state.getIncomingEdges().stream().filter(IIcfgReturnTransition.class::isInstance)
				.map(e -> new Triple<>((IReturnAction) e, (LOC) e.getTarget(),
						((IIcfgReturnTransition<LOC, ?>) e).getCallerProgramPoint()))
				.collect(Collectors.toList());
	}

	private <A extends IAction> Iterable<Pair<A, LOC>> getSuccessors(final LOC state, final Class<A> clazz) {
		return state.getIncomingEdges().stream().filter(clazz::isInstance)
				.map(e -> new Pair<>(clazz.cast(e), (LOC) e.getTarget())).collect(Collectors.toList());
	}

	private static final class IcfgHoareAnnotation<LOC extends IcfgLocation> implements IFloydHoareAnnotation<LOC> {
		@Override
		public IPredicate getPrecondition() {
			return null;
		}

		@Override
		public IPredicate getPostcondition() {
			return null;
		}

		@Override
		public IPredicate getAnnotation(final LOC state) {
			return HoareAnnotation.getAnnotation(state);
		}
	}
}