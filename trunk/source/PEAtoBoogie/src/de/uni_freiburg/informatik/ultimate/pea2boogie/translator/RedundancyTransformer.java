/*
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ReqParser plug-in.
 *
 * The ULTIMATE ReqParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ReqParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReqParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReqParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReqParer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqEffectStore;

public class RedundancyTransformer implements IReq2PeaTransformer {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;

	public RedundancyTransformer(final IUltimateServiceProvider services, final ILogger logger) {
		mLogger = logger;
		mServices = services;
	}

	public Map<PhaseEventAutomata, ReqEffectStore> getEffectStore() {
		return mPea2EffectStore;
	}

	@Override
	public IReq2Pea transform(final IReq2Pea req2pea, final List<DeclarationPattern> init,
			final List<PatternType<?>> requirements) {
		final RedundancyTransformerReq2Pea redundancyTransformerReq2Pea =
				new RedundancyTransformerReq2Pea(mServices, mLogger, init);
		redundancyTransformerReq2Pea.transform(req2pea);
		return redundancyTransformerReq2Pea;
	}
}
