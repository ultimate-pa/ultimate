package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.MultiPartialOrderInclusionCheck;

public class CegarLoopPartialOrderReduction<L extends IIcfgTransition<?>> extends BasicCegarLoop<L> {

	private final IIndependenceRelation<IPredicate, L>[] mRelations;

	public CegarLoopPartialOrderReduction(final DebugIdentifier name, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, taPrefs.interpolation(), false, services,
				compositionFactory, transitionClazz);
		mRelations = null; // TODO
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final MultiPartialOrderInclusionCheck<IPredicate, IPredicate, L> check = new MultiPartialOrderInclusionCheck<>(
				mRelations, (INestedWordAutomaton<L, IPredicate>) mAbstraction, mInterpolAutomaton);
		if (!check.getResult()) {
			mCounterexample = check.getCounterexample();
		}
		return check.getResult();
	}
}
