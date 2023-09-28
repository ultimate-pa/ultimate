package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder.SifaComponents;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class SifaSimplifierTransformer implements ITransformulaTransformer {
	// TODO: What is a reasonable timeout? And what to do if we exceed it?
	private static final long SIFA_TIMEOUT = 5 * 1000;
	private final IUltimateServiceProvider mServices;
	private Map<IcfgLocation, IPredicate> mSifaPredicates;

	public SifaSimplifierTransformer(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		final ILogger logger = mServices.getLoggingService().getLogger(getClass());
		// TODO: Can we reduce this number of locations?
		final Set<IcfgLocation> locations =
				icfg.getProgramPoints().values().stream().flatMap(x -> x.values().stream()).collect(Collectors.toSet());
		final SifaComponents sifa = new SifaBuilder(mServices, logger).construct((IIcfg<IcfgLocation>) icfg,
				mServices.getProgressMonitorService().getChildTimer(SIFA_TIMEOUT), locations);
		mSifaPredicates = sifa.getIcfgInterpreter().interpret();
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		// TODO Auto-generated method stub
		return null;
	}

	public Term backtranslate(final Term term) {
		// TODO: Implement
		return term;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		// TODO Auto-generated method stub
		return null;
	}

}
