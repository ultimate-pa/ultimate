package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PredicateTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.AtomicInterruptIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class InterruptIndependenceProviderFactory<L extends IIcfgTransition<?>> extends IndependenceProviderFactory<L> {

	public InterruptIndependenceProviderFactory(final IUltimateServiceProvider services, final TAPreferences pref,
			final ICopyActionFactory<L> copyFactory) {
		super(services, pref, copyFactory);
	}

	@Override
	protected IIndependenceRelation<IPredicate, L> constructIndependence(final IndependenceSettings settings,
			final boolean tfsAlreadyTransferred, final PredicateFactory predicateFactory,
			final PredicateTransferrer predicateTransferrer) {
		assert settings.getIndependenceType() == IndependenceType.SEMANTIC
				: "unsupported independence type for idp verification";
		return new AtomicInterruptIndependenceRelation<>(
				super.constructIndependence(settings, tfsAlreadyTransferred, predicateFactory, predicateTransferrer));
	}
}
