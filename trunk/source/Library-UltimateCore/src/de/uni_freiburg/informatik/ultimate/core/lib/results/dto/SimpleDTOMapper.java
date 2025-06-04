package de.uni_freiburg.informatik.ultimate.core.lib.results.dto;

import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.IResultWithCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Config;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Content;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Description;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Input;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Result;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.Setting;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.SimpleDTO;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.util.ToolchainUtils;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IFailedAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithFiniteTrace;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithInfiniteLassoTrace;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;

public final class SimpleDTOMapper implements IResultDTOMapper<SimpleDTO> {

	@Override
	public SimpleDTO transform(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results) {

		final Config config = new Config(ToolchainUtils.getPlugins(toolchain), getSettings(core));
		final Input input = getInput(toolchain);
		final Date time = Date.from(Instant.now());
		final Content content = new Content(core.getUltimateVersionString(), config, input, getResults(results));

		return new SimpleDTO(time, content);
	}

	private static Map<String, List<Setting>> getSettings(final ICore<RunDefinition> core) {
		// return core.getDiffPreferencesPerPlugin().entrySet().stream().filter(e -> !e.getValue().isEmpty())
		// .collect(Collectors.toMap(Entry::getKey, Entry::getValue));

		return core.getDiffPreferencesPerPlugin().entrySet().stream().filter(e -> !e.getValue().isEmpty())
				.collect(Collectors.toMap(Map.Entry::getKey, entry -> entry.getValue().stream()
						.map(e -> new Setting(e.getKey(), e.getValue())).collect(Collectors.toList())));
	}

	private static Input getInput(final IToolchain<RunDefinition> toolchain) {
		return new Input(Arrays.asList(toolchain.getInputFiles()).stream().map(file -> file.getAbsolutePath())
				.collect(Collectors.toList()));
	}

	private static Map<String, List<Result>> getResults(final Map<String, List<IResult>> results) {

		final Map<String, List<Result>> resultsData = new HashMap<>();

		for (final Entry<String, List<IResult>> entry : results.entrySet()) {
			final List<Result> pluginResults = new ArrayList<>();
			final String pluginName = entry.getKey();

			for (final IResult result : entry.getValue()) {

				final String resPlugin = result.getPlugin();
				final String resShortDesc = result.getShortDescription();
				final String resLongDesc = result.getLongDescription();

				if (result instanceof final IFailedAnalysisResult res) {
					// do nothing
				}

				if (result instanceof final IResultWithCheck res) {
					res.getCheckedSpecification();
				}

				if (result instanceof final IResultWithFiniteTrace res) {
					res.getFailurePath();
					res.getProgramExecution();
				}

				if (result instanceof final IResultWithInfiniteLassoTrace res) {
					res.getLasso();
					res.getStem();
				}

				if (result instanceof final IResultWithLocation res) {
					final ILocation loc = res.getLocation();
					loc.getAnnotationsAsMap();
					loc.getFileName();
					loc.getFunction();
					loc.getStartLine();
					loc.getEndLine();
					loc.getStartColumn();
					loc.getEndColumn();
				}

				if (result instanceof final IResultWithSeverity res) {
					res.getSeverity();
				}

				if (result instanceof final ITimeoutResult res) {
					// do nothing
				}

				// Do not handle classes here, only use methods defined by interfaces
				if (result instanceof final StatisticsResult res) {
					res.getStatistics();
				}

				final Description resDesc = new Description(resShortDesc, resLongDesc);
				pluginResults.add(new Result(resDesc, null));

			}

			resultsData.put(pluginName, pluginResults);
		}

		return resultsData;
	}
}
