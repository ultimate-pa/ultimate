package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

public class UltimateResultProcessor {

	public static void processUltimateResults(IUltimateServiceProvider services, JSONObject json) throws JSONException {
		// get Result from Ultimate
		HashMap<String, List<IResult>> results = services.getResultService().getResults();
		// add result to the json object
		ArrayList<JSONObject> resultList = new ArrayList<JSONObject>();
		for (List<IResult> rList : results.values()) {
			for (IResult r : rList) {
				String type = "UNDEF";
				UltimateResult packagedResult = new UltimateResult();
				if (r instanceof ExceptionOrErrorResult) {
					type = "ExceptionOrError";
					packagedResult.logLvl = "error";
				} else if (r instanceof CounterExampleResult) {
					type = "counter";
					packagedResult.logLvl = "error";
				} else if (r instanceof ProcedureContractResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof InvariantResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof PositiveResult) {
					type = "positive";
					packagedResult.logLvl = "info";
				} else if (r instanceof BenchmarkResult) {
					type = "benchmark";
					packagedResult.logLvl = "info";
				} else if (r instanceof TerminationArgumentResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof NonterminatingLassoResult<?, ?, ?>) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof AllSpecificationsHoldResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof UnprovableResult) {
					type = "unprovable";
					packagedResult.logLvl = "warning";
				} else if (r instanceof SyntaxErrorResult) {
					type = "syntaxError";
					packagedResult.logLvl = "error";
				} else if (r instanceof UnsupportedSyntaxResult) {
					type = "syntaxUnsupported";
					packagedResult.logLvl = "error";
				} else if (r instanceof TimeoutResultAtElement) {
					type = "timeout";
					packagedResult.logLvl = "error";
				} else if (r instanceof TypeErrorResult<?>) {
					type = "typeError";
					packagedResult.logLvl = "error";
				} else if (r instanceof IResultWithSeverity) {
					IResultWithSeverity rws = (IResultWithSeverity) r;
					if (rws.getSeverity().equals(Severity.ERROR)) {
						type = "error";
						packagedResult.logLvl = "error";
					} else if (rws.getSeverity().equals(Severity.WARNING)) {
						type = "warning";
						packagedResult.logLvl = "warning";
					} else if (rws.getSeverity().equals(Severity.INFO)) {
						type = "info";
						packagedResult.logLvl = "info";
					} else {
						throw new IllegalArgumentException("Unknown kind of severity.");
					}
				} else if (r instanceof NoResult<?>) {
					type = "noResult";
					packagedResult.logLvl = "warning";
				}
				// TODO : Add new "Out of resource" result here ...
				if (r instanceof IResultWithLocation) {
					ILocation loc = ((IResultWithLocation) r).getLocation();
					if (((IResultWithLocation) r).getLocation() == null) {
						throw new IllegalArgumentException("Location is null");
					}
					packagedResult.startLNr = loc.getStartLine();
					packagedResult.endLNr = loc.getEndLine();
					packagedResult.startCol = loc.getStartColumn();
					packagedResult.endCol = loc.getEndColumn();
				} else {
					packagedResult.startLNr = -1;
					packagedResult.endLNr = -1;
					packagedResult.startCol = -1;
					packagedResult.endCol = -1;
				}
				packagedResult.shortDesc = String.valueOf(r.getShortDescription());
				packagedResult.longDesc = String.valueOf(r.getLongDescription());
				packagedResult.type = type;
				resultList.add(new JSONObject(packagedResult));
			}
			json.put("results", new JSONArray(resultList.toArray(new JSONObject[0])));
		}
	}

}
