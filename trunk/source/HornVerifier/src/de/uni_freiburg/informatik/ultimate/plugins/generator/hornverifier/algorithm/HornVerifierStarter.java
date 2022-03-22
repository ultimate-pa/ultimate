package de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.algorithm;

import java.nio.file.Paths;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * Main class to analyze an icfg using horn-clauses.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HornVerifierStarter {
	public HornVerifierStarter(final IIcfg<IcfgLocation> icfg, final IUltimateServiceProvider services,
			final ILogger logger) {
		final ManagedScript script = HornVerifierUtils.createSolver(services, extractBasename(icfg), logger);
		final HornClauseSystem system = HornVerifierUtils.createHornClauses(icfg, script, 2);
		logger.info("Checking satisfiability of horn-clause system");
		final LBool sat = system.checkSat();
		logger.info("Finished. Result is " + sat);
	}

	private static String extractBasename(final IIcfg<IcfgLocation> icfg) {
		for (final IAnnotations a : icfg.getPayload().getAnnotations().values()) {
			if (a instanceof ILocation) {
				return Paths.get(((ILocation) a).getFileName()).getFileName().toString();
			}
		}
		// Fallback if no filename found
		return "dumped";
	}
}
