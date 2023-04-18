package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.IcfgToChcObserver.IChcProvider;

/**
 * ChcProvider for concurrent programs based on the petri-net using LBE.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ChcProviderConcurrentWithLbe implements IChcProvider {
	private static final int MAXIMUM_NUMBER_OF_THREADS = 2;

	private final ManagedScript mMgdScript;
	private final HcSymbolTable mHcSymbolTable;
	private final IUltimateServiceProvider mServices;

	public ChcProviderConcurrentWithLbe(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable,
			final IUltimateServiceProvider services) {
		mMgdScript = mgdScript;
		mHcSymbolTable = hcSymbolTable;
		mServices = services;
	}

	@Override
	public Collection<HornClause> getHornClauses(final IIcfg<IcfgLocation> icfg) {
		final var reduced = new IcfgLiptonReducer(mServices, icfg, MAXIMUM_NUMBER_OF_THREADS).getResult();
		return new ChcProviderConcurrent(mMgdScript, mHcSymbolTable, ConcurrencyMode.SINGLE_MAIN_THREAD, MAXIMUM_NUMBER_OF_THREADS)
				.getHornClauses(reduced);
	}
}
