package de.uni_freiburg.informatik.ultimate.servercontroller.converter;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.Converter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.servercontroller.ServerController.ResultsWrapper;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Confirm;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.File;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Location;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Result;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ResultSummary;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Results;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolChainResult;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolchainResults;

public class ControllerConverter extends Converter<GeneratedMessageV3, Object> {
	public static ControllerConverter get(IUltimateServiceProvider services) {
		return new ControllerConverter(services);
	}

	protected ControllerConverter(IUltimateServiceProvider services) {
		super(services, Object.class);
	}

	private static Controller.StackTraceElement convertStackTraceElement(StackTraceElement el) {
		return Controller.StackTraceElement.newBuilder().setDeclaringClass(el.getClassName())
				.setFileName(el.getFileName()).setMethodName(el.getMethodName()).setLineNumber(el.getLineNumber())
				.build();
	}

	private static Result convertResult(IResult result) {
		Result.Builder builder = Result.newBuilder();
		builder.setPlugin(result.getPlugin()).setShortDescription(result.getShortDescription())
				.setResultClassName(result.getClass().getSimpleName()).setLongDescription(result.getLongDescription());
		if (result instanceof IResultWithLocation) {
			final ILocation loc = ((IResultWithLocation) result).getLocation();
			builder.setLocation(convertLocation(loc));
		}
		return builder.build();
	}

	private static Location convertLocation(ILocation location) {
		final Location.Builder builder = Location.newBuilder();
		builder.setFileName(location.getFileName()).setStartCol(location.getStartColumn())
				.setEndCol(location.getEndColumn()).setStartLine(location.getStartLine())
				.setEndLine(location.getEndLine());
		return builder.build();
	}

	private static Results convertResults(List<IResult> results) {
		final Results.Builder builder = Results.newBuilder();
		results.stream().map(ControllerConverter::convertResult).forEach(builder::addResults);
		return builder.build();
	}

	private static File convertFile(final java.io.File file) {
		final File.Builder builder = File.newBuilder();
		builder.setFileName(file.getName());

		Path path = Paths.get(file.getAbsolutePath());
		try {
			final String content = new String(Files.readAllBytes(path));
			builder.setContent(content);
		} catch (IOException e) {
		}

		return builder.build();
	}

	private static Boolean toBoolean(final Confirm confirm) {
		return confirm.getOk();
	}

	@Override
	protected void init(ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(ResultSummary.class, ResultSummarizer.class, rs -> {
			return ResultSummary.newBuilder().setDescription(rs.getResultDescription())
					.setResult(ToolChainResult.valueOf(rs.getResultSummary().toString())).build();
		});

		converterRegistry.registerBA(ToolchainResults.class, ResultsWrapper.class, rs -> {
			ToolchainResults.Builder builder = ToolchainResults.newBuilder();
			rs.results.entrySet().stream().forEach(e -> builder.putResults(e.getKey(), convertResults(e.getValue())));
			return builder.build();
		});

		converterRegistry.registerBA(Controller.Exception.class, Throwable.class, e -> {
			final Controller.Exception.Builder builder =
					Controller.Exception.newBuilder().setClass_(e.getClass().getName());
			Arrays.stream(e.getStackTrace()).map(ControllerConverter::convertStackTraceElement)
					.forEach(builder::addStackTrace);
			if (e.getMessage() != null)
				builder.setMessage(e.getMessage());
			return builder.build();
		});

		converterRegistry.registerBA(File.class, java.io.File.class, ControllerConverter::convertFile);

		converterRegistry.registerAB(Confirm.class, Boolean.class, ControllerConverter::toBoolean);
	}
}
