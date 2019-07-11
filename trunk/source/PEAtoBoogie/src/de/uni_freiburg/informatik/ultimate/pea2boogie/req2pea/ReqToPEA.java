/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder.TypeErrorInfo;

public class ReqToPEA {
	private static final boolean ENABLE_DEBUG_LOGS = false;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final PeaResultUtil mResult;
	private final Set<String> mConstIds;
	private final Map<PatternType, PhaseEventAutomata> mPattern2Peas;
	private final IReqSymbolTable mSymbolTable;
	private final Map<String, TypeErrorInfo> mTypeErrors;

	public ReqToPEA(final IUltimateServiceProvider services, final ILogger logger,
			final List<InitializationPattern> init, final List<PatternType> requirements,
			final Map<String, Integer> id2bounds) {
		mLogger = logger;
		mServices = services;
		mResult = new PeaResultUtil(mLogger, mServices);

		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);

		for (final PatternType pattern : init) {
			if (pattern instanceof InitializationPattern) {
				builder.addInitPattern((InitializationPattern) pattern);
			}
		}

		mConstIds = builder.getConstIds();
		mPattern2Peas = generatePeas(requirements, id2bounds);

		for (final Entry<PatternType, PhaseEventAutomata> entry : mPattern2Peas.entrySet()) {
			builder.addPea(entry.getKey(), entry.getValue());
		}

		mSymbolTable = builder.constructSymbolTable();
		mTypeErrors = builder.getTypeErrors();
	}

	public Map<PatternType, PhaseEventAutomata> getPattern2Peas() {
		return Collections.unmodifiableMap(mPattern2Peas);
	}

	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	public Map<String, TypeErrorInfo> getTypeErrors() {
		return mTypeErrors;
	}

	private Map<PatternType, PhaseEventAutomata> generatePeas(final List<PatternType> patterns,
			final Map<String, Integer> id2bounds) {
		final Map<PatternType, PhaseEventAutomata> req2automata = new LinkedHashMap<>();
		final PatternToPEA peaTrans = new PatternToPEA(mLogger, mConstIds);
		mLogger.info(String.format("Transforming %s requirements to PEAs", patterns.size()));

		final Map<Class<?>, Integer> counter = new HashMap<>();

		for (final PatternType pat : patterns) {

			final PhaseEventAutomata pea;
			try {
				if (ENABLE_DEBUG_LOGS) {
					mLogger.info("Transforming " + pat.getId());
				}
				counter.compute(pat.getClass(), (a, b) -> b == null ? 1 : b + 1);
				pea = pat.transformToPea(peaTrans, id2bounds);
			} catch (final Exception ex) {
				final String reason = ex.getMessage() == null ? ex.getClass().toString() : ex.getMessage();
				mResult.transformationError(pat, reason);
				continue;
			}
			if (pea.getInit().length == 0) {
				mResult.transformationError(pat, "No initial phase");
				continue;
			}
			final PhaseEventAutomata old = req2automata.put(pat, pea);
			if (old != null) {
				mResult.transformationError(pat, "Duplicate automaton: " + old.getName() + " and " + pea.getName());
				continue;
			}
		}
		mLogger.info("Following types of requirements were processed");
		for (final Entry<Class<?>, Integer> entry : counter.entrySet()) {
			mLogger.info(entry.getKey() + " : " + entry.getValue());
		}

		mLogger.info(String.format("Finished transforming %s requirements to PEAs", patterns.size()));

		return req2automata;
	}

	public void genPEAforUPPAAL(final PatternType[] patterns, final String xmlFilePath,
			final Map<String, Integer> id2bounds) {

		PhaseEventAutomata pea = null;

		final PatternToPEA peaTrans = new PatternToPEA(mLogger, mConstIds);

		for (final PatternType pat : patterns) {
			if (pea == null) {
				pea = pat.transformToPea(peaTrans, id2bounds);

			} else {
				final PhaseEventAutomata pea2 = pat.transformToPea(peaTrans, id2bounds);
				if (pea2 == null) {
					continue;
				}
				pea = pea.parallel(pea2);

			}
		}
		final J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
		uppaalConverter.writePEA2UppaalFile(xmlFilePath, pea);
	}

}
