package de.uni_freiburg.informatik.ultimate.servercontroller.converter;

import java.util.List;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.AbstractConverter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.servercontroller.ServerController.ResultsWrapper;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Location;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Result;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ResultSummary;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Results;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolChainResult;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolchainResults;

public class ControllerConverter extends AbstractConverter<GeneratedMessageV3, Object> {
	public static ControllerConverter get(final ILogger logger) {
		return new ControllerConverter(logger);
	}

	protected ControllerConverter(final IUltimateServiceProvider services) {
		super(services, Object.class);
	}

	protected ControllerConverter(final ILogger logger) {
		super(logger, Object.class);
	}

	private static Result convertResult(final IResult result) {
		final Result.Builder builder = Result.newBuilder();
		builder.setPlugin(result.getPlugin()).setShortDescription(result.getShortDescription())
				.setResultClassName(result.getClass().getSimpleName()).setLongDescription(result.getLongDescription());
		if (result instanceof IResultWithLocation) {
			final ILocation loc = ((IResultWithLocation) result).getLocation();
			builder.setLocation(convertLocation(loc));
		}
		return builder.build();
	}

	private static Location convertLocation(final ILocation location) {
		final Location.Builder builder = Location.newBuilder();
		builder.setFileName(location.getFileName()).setStartCol(location.getStartColumn())
				.setEndCol(location.getEndColumn()).setStartLine(location.getStartLine())
				.setEndLine(location.getEndLine());
		return builder.build();
	}

	private static Results convertResults(final List<IResult> results) {
		final Results.Builder builder = Results.newBuilder();
		results.stream().map(ControllerConverter::convertResult).forEach(builder::addResults);
		return builder.build();
	}

	@Override
	protected void init(final ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(ResultSummary.class, ResultSummarizer.class, rs -> {
			return ResultSummary.newBuilder().setDescription(rs.getResultDescription())
					.setResult(ToolChainResult.valueOf(rs.getResultSummary().toString())).build();
		});

		converterRegistry.registerBA(ToolchainResults.class, ResultsWrapper.class, rs -> {
			final ToolchainResults.Builder builder = ToolchainResults.newBuilder();
			rs.results.entrySet().stream().forEach(e -> builder.putResults(e.getKey(), convertResults(e.getValue())));
			builder.setInputFileName(rs.inputFile.getName());
			return builder.build();
		});
	}
}
