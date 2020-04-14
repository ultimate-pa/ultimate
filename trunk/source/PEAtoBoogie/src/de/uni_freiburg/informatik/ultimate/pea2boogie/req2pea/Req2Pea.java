/*
 * Copyright (C) 2017-2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2019 University of Freiburg
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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder.ErrorInfo;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder.ErrorType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Req2Pea implements IReq2Pea {
	private static final boolean ENABLE_DEBUG_LOGS = false;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final PeaResultUtil mResultUtil;
	private final Map<PatternType, ReqPeas> mPattern2Peas;
	private final IReqSymbolTable mSymbolTable;
	private final boolean mHasErrors;

	public Req2Pea(final IUltimateServiceProvider services, final ILogger logger,
			final List<InitializationPattern> init, final List<PatternType> requirements) {
		mLogger = logger;
		mServices = services;
		mResultUtil = new PeaResultUtil(mLogger, mServices);

		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);

		for (final InitializationPattern pattern : init) {
			if (pattern instanceof InitializationPattern) {
				builder.addInitPattern(pattern);
			}
		}
		final Map<String, Integer> id2bounds = builder.getId2Bounds();
		mPattern2Peas = generatePeas(requirements, id2bounds);

		for (final Entry<PatternType, ReqPeas> entry : mPattern2Peas.entrySet()) {
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : entry.getValue().getCounterTrace2Pea()) {
				builder.addPea(entry.getKey(), pea.getValue());
			}
		}

		mSymbolTable = builder.constructSymbolTable();
		final Set<Entry<String, ErrorInfo>> errors = builder.getErrors();
		for (final Entry<String, ErrorInfo> entry : errors) {
			if (entry.getValue().getType() == ErrorType.SYNTAX_ERROR) {
				final BoogieLocation loc = mSymbolTable.getLocations().get(entry.getValue().getSource());
				mResultUtil.syntaxError(loc, entry.getValue().getMessage());
			} else {
				final String msg = entry.getValue().getType().toString() + " of " + entry.getKey();
				mResultUtil.typeError(entry.getValue().getSource(), msg);
			}
		}
		mHasErrors = !errors.isEmpty();
	}

	@Override
	public Map<PatternType, ReqPeas> getPattern2Peas() {
		return Collections.unmodifiableMap(mPattern2Peas);
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	private Map<PatternType, ReqPeas> generatePeas(final List<PatternType> patterns,
			final Map<String, Integer> id2bounds) {
		final Map<PatternType, ReqPeas> req2automata = new LinkedHashMap<>();
		mLogger.info(String.format("Transforming %s requirements to PEAs", patterns.size()));

		final Map<Class<?>, Integer> counter = new HashMap<>();

		for (final PatternType pat : patterns) {
			final ReqPeas pea;
			try {
				if (ENABLE_DEBUG_LOGS) {
					mLogger.info("Transforming " + pat.getId());
				}
				counter.compute(pat.getClass(), (a, b) -> b == null ? 1 : b + 1);
				pea = pat.transformToPea(mLogger, id2bounds);
			} catch (final Exception ex) {
				final String reason = ex.getMessage() == null ? ex.getClass().toString() : ex.getMessage();
				mResultUtil.transformationError(pat, reason);
				continue;
			}

			if (pea.getCounterTrace2Pea().stream().map(Entry::getValue).anyMatch(a -> a.getInit().length == 0)) {
				mResultUtil.transformationError(pat, "A PEA is missing its initial phase");
				continue;
			}
			final ReqPeas old = req2automata.put(pat, pea);
			if (old != null) {
				final String msg = String.format("Duplicate automata: %s and %s",
						old.getCounterTrace2Pea().stream().map(a -> a.getValue().getName())
								.collect(Collectors.joining(",")),
						pea.getCounterTrace2Pea().stream().map(Entry::getValue).map(PhaseEventAutomata::getName)
								.collect(Collectors.joining(",")));
				mResultUtil.transformationError(pat, msg);
			}
		}
		mLogger.info("Following types of requirements were processed");
		for (final Entry<Class<?>, Integer> entry : counter.entrySet()) {
			mLogger.info(entry.getKey() + " : " + entry.getValue());
		}

		mLogger.info(String.format("Finished transforming %s requirements to PEAs", patterns.size()));

		return req2automata;
	}

	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public void transform(final IReq2Pea previous) {
		// do nothing, as this IReq2Pea should generate new Peas from reqs and do not do any transformation.
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqCheckAnnotator(mServices, mLogger, mPattern2Peas, mSymbolTable);
	}
}
