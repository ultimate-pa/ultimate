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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
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
	private final List<ReqPeas<CDD>> mPattern2Peas;
	private final IReqSymbolTable mSymbolTable;
	private final boolean mHasErrors;
	private final Durations mDurations;

	public Req2Pea(final IUltimateServiceProvider services, final ILogger logger, final List<DeclarationPattern> init,
			final List<PatternType<?>> reqs) {
		mLogger = logger;
		mServices = services;
		mResultUtil = new PeaResultUtil(mLogger, mServices);

		final List<PatternType<?>> requirements = replacePrev(reqs);
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);

		mDurations = new Durations();
		for (final DeclarationPattern pattern : init) {
			builder.addInitPattern(pattern);
			mDurations.addInitPattern(pattern);
		}
		reqs.stream().forEach(mDurations::addNonInitPattern);
		mPattern2Peas = generatePeas(requirements, mDurations);

		for (final ReqPeas<CDD> reqpea : mPattern2Peas) {
			for (final Entry<CounterTrace, PhaseEventAutomata<CDD>> pea : reqpea.getCounterTrace2Pea()) {
				builder.addPea(reqpea.getPattern(), pea.getValue());
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

	/**
	 * Replace FunctionAplication 'prev()' in scope and CDDs of all requirements.
	 *
	 * @param requirements
	 */
	private List<PatternType<?>> replacePrev(final List<PatternType<?>> requirements) {
		final List<PatternType<?>> rtr = new ArrayList<>(requirements.size());
		final CDDTransformer cddTransformer = new CDDTransformer();
		for (final PatternType<?> req : requirements) {

			final SrParseScope<?> scope = req.getScope().create(cddTransformer.transform(req.getScope().getCdd1()),
					cddTransformer.transform(req.getScope().getCdd2()));
			final List<CDD> cdds = req.getCdds().stream().map(cddTransformer::transform).collect(Collectors.toList());
			rtr.add(req.create(scope, req.getId(), cdds, req.getDurations(), req.getDurationNames()));
		}
		return rtr;
	}

	@Override
	public List<ReqPeas<CDD>> getReqPeas() {
		return Collections.unmodifiableList(mPattern2Peas);
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	private List<ReqPeas<CDD>> generatePeas(final List<PatternType<?>> patterns, final Durations durations) {
		final Map<PatternType<?>, ReqPeas<CDD>> req2automata = new LinkedHashMap<>();
		mLogger.info(String.format("Transforming %s requirements to PEAs", patterns.size()));

		final Map<Class<?>, Integer> counter = new HashMap<>();

		for (final PatternType<?> pat : patterns) {
			final ReqPeas<CDD> pea;
			try {
				if (ENABLE_DEBUG_LOGS) {
					mLogger.info("Transforming " + pat.getId());
				}
				counter.compute(pat.getClass(), (a, b) -> b == null ? 1 : b + 1);
				pea = pat.transformToPea(mLogger, durations);
			} catch (final Exception ex) {
				final String reason = ex.getMessage() == null ? ex.getClass().toString() : ex.getMessage();
				mResultUtil.transformationError(pat, reason);
				continue;
			}

			if (pea.getCounterTrace2Pea().stream().map(Entry::getValue).anyMatch(a -> a.getInit().length == 0)) {
				mResultUtil.transformationError(pat, "A PEA is missing its initial phase");
				continue;
			}
			final ReqPeas<CDD> old = req2automata.put(pat, pea);
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

		return req2automata.entrySet().stream().map(a -> a.getValue()).collect(Collectors.toList());
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
		return new ReqCheckAnnotator(mServices, mLogger, mPattern2Peas, mSymbolTable, mDurations);
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

	/**
	 * Transform a {@link CDD} such that occurrences of {@link FunctionApplication} 'prev()' in
	 * {@link BoogieBooleanExpressionDecision} are replaced by the old value of its argument.
	 *
	 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
	 */
	private final class CDDTransformer {

		public CDD transform(final CDD cdd) {
			if (cdd == null || cdd == CDD.TRUE || cdd == CDD.FALSE) {
				return cdd;
			}

			// Traverse the given CDD.
			final CDD[] childs = cdd.getChilds();
			for (int i = 0; i < childs.length; i++) {
				childs[i] = transform(childs[i]);
			}

			// Transform BoogieBooleanExpressionDecision.
			Decision<?> decision = cdd.getDecision();
			if (decision instanceof BoogieBooleanExpressionDecision) {
				final Expression expr = ((BoogieBooleanExpressionDecision) decision).getExpression()
						.accept(new PrevFunctionApplicationTransformer());
				decision = BoogieBooleanExpressionDecision.createWithoutReduction(expr).getDecision();
			}

			return CDD.create(decision, childs);
		}
	}

	/**
	 * Replace any {@link FunctionApplication} 'prev()' by the old value of its argument.
	 *
	 * @throws IllegalArgumentException
	 *             if the number of arguments is not exactly one.
	 *
	 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
	 */
	private final class PrevFunctionApplicationTransformer extends GeneratedBoogieAstTransformer {

		@Override
		public Expression transform(final FunctionApplication node) {
			if (!node.getIdentifier().equals("prev")) {
				return node;
			}

			final Expression[] args = node.getArguments();
			if (args.length != 1) {
				throw new IllegalArgumentException(
						"Unexpected number of arguments for FunctionApplication: " + args.length);
			}

			return args[0].accept(new PrevFunctionApplicationArgumentTransformer());
		}

		/**
		 * Replace any {@link IdentifierExpression} by its old value.
		 *
		 * @throws IllegalArgumentException
		 *             if there exist a {@link FunctionApplication} 'prev()'.
		 *
		 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
		 */
		private final class PrevFunctionApplicationArgumentTransformer extends GeneratedBoogieAstTransformer {

			@Override
			public Expression transform(final FunctionApplication node) {
				if (node.getIdentifier().equals("prev")) {
					throw new IllegalArgumentException("Unsupported nested FunctionApplication prev().");
				}
				return node;
			}

			@Override
			public Expression transform(final IdentifierExpression node) {
				return new IdentifierExpression(node.getLoc(), node.getType(), "'" + node.getIdentifier(),
						node.getDeclarationInformation());
			}
		}
	}
}
