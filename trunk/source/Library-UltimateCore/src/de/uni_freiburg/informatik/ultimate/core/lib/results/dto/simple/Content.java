package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import java.util.List;
import java.util.Map;

import com.google.gson.annotations.SerializedName;

/**
 * <code>
 * time: 2025-01-17 10:18,
 * ultimate: {
 *   version: 0.3.0,
 *   config: {
 *     toolchain: [
 *       de.uni_freiburg.informatik.ultimate.traceabstraction,
 *       de.uni_freiburg.informatik.ultimate.resultprinter
 *     ],
 *     settings: [
 *       DIV_BY_ZERO=ASSERTandASSUME
 *     ]
 *   },
 *   input: {
 *     files: [
 *       /home/arch/test/main.c
 *     ]
 *   },
 *   results: [
 *     de.uni_freiburg.informatik.ultimate.resultprinter: [
 *       {
 *         type: statistics
 *         numTraces: ...
 *       },
 *       {
 *         ...
 *       }
 *     ]
 *   ]
 * }
 * </code>
 */
public final class Content {

	@SerializedName("version")
	final String mVersion;

	@SerializedName("config")
	final Config mConfig;

	@SerializedName("input")
	final Input mInput;

	@SerializedName("results")
	final Map<String, List<Result>> mResults;

	public Content(final String version, final Config config, final Input input,
			final Map<String, List<Result>> results) {
		mVersion = version;
		mConfig = config;
		mInput = input;
		mResults = results;
	}

	public String getVersion() {
		return mVersion;
	}

	public Config getConfig() {
		return mConfig;
	}

	public Input getInput() {
		return mInput;
	}

	public Map<String, List<Result>> getResults() {
		return mResults;
	}
}
