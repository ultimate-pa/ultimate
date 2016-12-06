package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class UltimateResultProcessor {

	private static final String TYPE_INVARIANT = "invariant";
	private static final String LVL_WARNING = "warning";
	private static final String LVL_INFO = "info";
	private static final String LVL_ERROR = "error";

	public static void processUltimateResults(final IUltimateServiceProvider services, final JSONObject json)
			throws JSONException {
		// get Result from Ultimate
		final Map<String, List<IResult>> results = services.getResultService().getResults();
		// add result to the json object
		final List<JSONObject> resultList = new ArrayList<>();
		for (final List<IResult> rList : results.values()) {
			for (final IResult r : rList) {
				SimpleLogger.log("processing result " + r.getShortDescription());
				String type = "UNDEF";
				final UltimateResult packagedResult = new UltimateResult();
				if (r instanceof ExceptionOrErrorResult) {
					type = "ExceptionOrError";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof CounterExampleResult) {
					type = "counter";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof ProcedureContractResult) {
					type = TYPE_INVARIANT;
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof InvariantResult) {
					type = TYPE_INVARIANT;
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof PositiveResult) {
					type = "positive";
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof BenchmarkResult) {
					type = "benchmark";
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof TerminationArgumentResult) {
					type = TYPE_INVARIANT;
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof NonterminatingLassoResult<?, ?, ?>) {
					type = TYPE_INVARIANT;
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof AllSpecificationsHoldResult) {
					type = TYPE_INVARIANT;
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof UnprovableResult) {
					type = "unprovable";
					packagedResult.logLvl = LVL_WARNING;
				} else if (r instanceof SyntaxErrorResult) {
					type = "syntaxError";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof UnsupportedSyntaxResult) {
					type = "syntaxUnsupported";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof TimeoutResultAtElement) {
					type = "timeout";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof TypeErrorResult<?>) {
					type = "typeError";
					packagedResult.logLvl = LVL_ERROR;
				} else if (r instanceof TerminationAnalysisResult) {
					type = "positive";
					packagedResult.logLvl = LVL_INFO;
				} else if (r instanceof IResultWithSeverity) {
					final IResultWithSeverity rws = (IResultWithSeverity) r;
					if (rws.getSeverity().equals(Severity.ERROR)) {
						type = LVL_ERROR;
						packagedResult.logLvl = LVL_ERROR;
					} else if (rws.getSeverity().equals(Severity.WARNING)) {
						type = LVL_WARNING;
						packagedResult.logLvl = LVL_WARNING;
					} else if (rws.getSeverity().equals(Severity.INFO)) {
						type = LVL_INFO;
						packagedResult.logLvl = LVL_INFO;
					} else {
						throw new IllegalArgumentException("Unknown kind of severity.");
					}
				} else if (r instanceof NoResult<?>) {
					type = "noResult";
					packagedResult.logLvl = LVL_WARNING;
				}

				// TODO : Add new "Out of resource" result here ...
				if (r instanceof IResultWithLocation) {
					final ILocation loc = ((IResultWithLocation) r).getLocation();
					if (loc == null) {
						SimpleLogger.log("IResultWithLocation with getLocation()==null, ignoring...");
						setEmptyLocation(packagedResult);
					} else {
						packagedResult.startLNr = loc.getStartLine();
						packagedResult.endLNr = loc.getEndLine();
						packagedResult.startCol = loc.getStartColumn();
						packagedResult.endCol = loc.getEndColumn();
					}
				} else {
					setEmptyLocation(packagedResult);
				}
				packagedResult.shortDesc = String.valueOf(r.getShortDescription());
				packagedResult.longDesc = String.valueOf(r.getLongDescription());
				packagedResult.type = type;
				resultList.add(new JSONObject(packagedResult));
				SimpleLogger.log("added result: " + packagedResult.toString());
			}
			json.put("results", new JSONArray(resultList.toArray(new JSONObject[resultList.size()])));
		}
	}

	private static void setEmptyLocation(final UltimateResult packagedResult) {
		packagedResult.startLNr = -1;
		packagedResult.endLNr = -1;
		packagedResult.startCol = -1;
		packagedResult.endCol = -1;
	}

}
