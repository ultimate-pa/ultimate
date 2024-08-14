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

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEAComplement;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqCheckAnnotator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class RedundancyTransformerReq2Pea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Durations mDurations;

	public RedundancyTransformerReq2Pea(final IUltimateServiceProvider services, final ILogger logger,
			final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mReqPeas = new ArrayList<>();
		mDurations = new Durations();
	}

	@Override
	public void transform(final IReq2Pea req2pea) {
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mServices, mLogger);
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		mSymbolTable = symbolTable;
		final Set<String> constVars = mSymbolTable.getConstVars();

		for (final DeclarationPattern p : mInitPattern) {
			builder.addInitPattern(p);
			mDurations.addInitPattern(p);
		}

		final List<ReqPeas> peas = req2pea.getReqPeas();
		for (final ReqPeas reqPea : peas) {
			final PatternType<?> pattern = reqPea.getPattern();
			final List<Entry<CounterTrace, PhaseEventAutomata>> ct2pea = reqPea.getCounterTrace2Pea();

			final List<Entry<CounterTrace, PhaseEventAutomata>> totalCt2pea = new ArrayList<>();

			for (final Entry<CounterTrace, PhaseEventAutomata> pea : ct2pea) {
				final PhaseEventAutomata peaToComplement = pea.getValue();
				final PEAComplement complementPea = new PEAComplement(peaToComplement, constVars);
				final PhaseEventAutomata totalisedPea = complementPea.getTotalisedPEA();

				totalCt2pea.add(new Pair<>(pea.getKey(), totalisedPea));
				builder.addPea(pattern, totalisedPea);

			}
			mReqPeas.add(new ReqPeas(pattern, totalCt2pea));
		}
		mSymbolTable = builder.constructSymbolTable();
	}

	@Override
	public List<ReqPeas> getReqPeas() {
		return mReqPeas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqCheckAnnotator(mServices, mLogger, mReqPeas, mSymbolTable, mDurations);
	}

}