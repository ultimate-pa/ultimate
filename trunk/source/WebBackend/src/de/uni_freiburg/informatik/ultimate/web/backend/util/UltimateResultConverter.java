package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.UltimateResult;

public class UltimateResultConverter {

	private static final String TYPE_INVARIANT = "invariant";
	private static final String LVL_WARNING = "warning";
	private static final String LVL_INFO = "info";
	private static final String LVL_ERROR = "error";

	private UltimateResultConverter() {
		// do not instantiate utility class
	}

	public static List<UltimateResult> processUltimateResults(final ILogger logger,
			final IUltimateServiceProvider services) {
		// get Result from Ultimate
		final Map<String, List<IResult>> results = services.getResultService().getResults();
		// add result to the json object
		final List<UltimateResult> rtr = new ArrayList<>();
		for (final Entry<String, List<IResult>> entry : results.entrySet()) {
			final List<IResult> toolResults = entry.getValue();
			for (final IResult result : toolResults) {
				if (result instanceof StatisticsResult<?>) {
					logger.info("Skipping result " + result.getLongDescription());
					continue;
				}
				final UltimateResult resultDto = processResult(logger, result);
				rtr.add(resultDto);
				logger.info("Added result: %s", resultDto);
			}
		}
		return rtr;
	}

	public static UltimateResult processResult(final ILogger logger, final IResult r) {
		logger.info("Processing result " + r.getShortDescription());
		final String type;
		final String logLvl;
		if (r instanceof ExceptionOrErrorResult) {
			type = "ExceptionOrError";
			logLvl = LVL_ERROR;
		} else if (r instanceof CounterExampleResult || r instanceof NonterminatingLassoResult<?, ?, ?>
				|| r instanceof NonTerminationArgumentResult<?, ?>) {
			type = "counter";
			logLvl = LVL_ERROR;
		} else if (r instanceof TerminationAnalysisResult) {
			switch (((TerminationAnalysisResult) r).getTermination()) {
			case NONTERMINATING:
				type = "counter";
				logLvl = LVL_ERROR;
				break;
			case TERMINATING:
				type = "positive";
				logLvl = LVL_INFO;
				break;
			default:
				type = "unknown";
				logLvl = LVL_WARNING;
				break;
			}
		} else if (r instanceof ProcedureContractResult || r instanceof InvariantResult
				|| r instanceof TerminationArgumentResult) {
			type = TYPE_INVARIANT;
			logLvl = LVL_INFO;
		} else if (r instanceof PositiveResult || r instanceof AllSpecificationsHoldResult) {
			type = "positive";
			logLvl = LVL_INFO;
		} else if (r instanceof StatisticsResult) {
			type = "benchmark";
			logLvl = LVL_INFO;
		} else if (r instanceof UnprovableResult) {
			type = "unprovable";
			logLvl = LVL_WARNING;
		} else if (r instanceof SyntaxErrorResult) {
			type = "syntaxError";
			logLvl = LVL_ERROR;
		} else if (r instanceof UnsupportedSyntaxResult) {
			type = "syntaxUnsupported";
			logLvl = LVL_ERROR;
		} else if (r instanceof TimeoutResultAtElement) {
			type = "timeout";
			logLvl = LVL_ERROR;
		} else if (r instanceof TypeErrorResult<?>) {
			type = "typeError";
			logLvl = LVL_ERROR;
		} else if (r instanceof IResultWithSeverity) {
			final IResultWithSeverity rws = (IResultWithSeverity) r;
			if (rws.getSeverity().equals(Severity.ERROR)) {
				type = LVL_ERROR;
				logLvl = LVL_ERROR;
			} else if (rws.getSeverity().equals(Severity.WARNING)) {
				type = LVL_WARNING;
				logLvl = LVL_WARNING;
			} else if (rws.getSeverity().equals(Severity.INFO)) {
				type = LVL_INFO;
				logLvl = LVL_INFO;
			} else {
				throw new IllegalArgumentException("Unknown kind of severity.");
			}
		} else if (r instanceof NoResult<?>) {
			type = "noResult";
			logLvl = LVL_WARNING;
		} else {
			type = "UNDEF";
			logLvl = LVL_INFO;
		}

		final UltimateResult packagedResult = new UltimateResult();

		packagedResult.setLogLvl(logLvl);
		if (r instanceof IResultWithLocation) {
			final ILocation loc = ((IResultWithLocation) r).getLocation();
			if (loc == null) {
				logger.info("IResultWithLocation with getLocation()==null, ignoring...");
				setEmptyLocation(packagedResult);
			} else {
				packagedResult.setStartLNr(loc.getStartLine());
				packagedResult.setEndLNr(loc.getEndLine());
				packagedResult.setStartCol(loc.getStartColumn());
				packagedResult.setEndCol(loc.getEndColumn());
			}
		} else {
			setEmptyLocation(packagedResult);
		}
		packagedResult.setShortDesc(r.getShortDescription());
		packagedResult.setLongDesc(r.getLongDescription());
		packagedResult.setType(type);
		return packagedResult;
	}

	private static void setEmptyLocation(final UltimateResult packagedResult) {
		packagedResult.setStartLNr(-1);
		packagedResult.setEndLNr(-1);
		packagedResult.setStartCol(-1);
		packagedResult.setEndCol(-1);
	}

}
