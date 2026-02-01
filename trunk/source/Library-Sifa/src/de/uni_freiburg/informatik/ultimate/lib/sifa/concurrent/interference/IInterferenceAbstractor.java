package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IInterferenceAbstractor {

	IInterferenceAbstraction abstractTransitionsToInterferenceAbstraction(
			Map<String, Map<IcfgLocation, IPredicate>> analysisResults, Map<String, IIcfg<IcfgLocation>> threadIcfgs);
}
