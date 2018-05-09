/*
 * Copyright (C) 2018 Jonas Werner (jonaswerner95@gmail.com)
 *
 * This file is part of the ULTIMATE PDR library .
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PDR library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PDR library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pdr;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;

/**
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class Pdr<LOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public Pdr(final ILogger logger, final IUltimateServiceProvider services, final Object settings) {
		mLogger = logger;
		mServices = services;
	}

	PdrResult computePdr(final IIcfg<LOC> icfg, final IPredicateUnifier predicateUnifier) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		final ManagedScript mgdScript = csToolkit.getManagedScript();
		final BasicPredicateFactory predicateFac = predicateUnifier.getPredicateFactory();
		final PredicateTransformer predTrans =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(mServices, mgdScript));
		return null;
	}

	private final class PdrResult {
		Map<LOC, Map<LOC, IPredicate>> mPredicates;
		Map<LOC, IcfgProgramExecution> mCounterexamples;
	}

}
