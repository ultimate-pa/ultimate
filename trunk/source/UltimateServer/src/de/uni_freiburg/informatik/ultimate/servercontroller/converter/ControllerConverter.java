package de.uni_freiburg.informatik.ultimate.servercontroller.converter;

import java.util.Arrays;
import java.util.List;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.Converter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.servercontroller.ServerController.ResultsWrapper;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Result;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ResultSummary;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Results;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolChainResult;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolchainResults;

public class ControllerConverter extends Converter<GeneratedMessageV3, Object> {
	public static ControllerConverter get() {
		return new ControllerConverter();
	}

	protected ControllerConverter() {
		super(Object.class);
	}

	private static Controller.StackTraceElement convertStackTraceElement(StackTraceElement el) {
		return Controller.StackTraceElement.newBuilder().setDeclaringClass(el.getClassName())
				.setFileName(el.getFileName()).setMethodName(el.getMethodName()).setLineNumber(el.getLineNumber())
				.build();
	}

	private static Result convertResult(IResult result) {
		return Result.newBuilder().setPlugin(result.getPlugin()).setShortDescription(result.getShortDescription())
				.setLongDescription(result.getLongDescription()).build();
	}

	private static Results convertResults(List<IResult> results) {
		final Results.Builder builder = Results.newBuilder();
		results.stream().map(ControllerConverter::convertResult).forEach(builder::addResults);
		return builder.build();
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
			final Controller.Exception.Builder builder = Controller.Exception.newBuilder().setClass_(e.getClass().getName());
			Arrays.stream(e.getStackTrace()).map(ControllerConverter::convertStackTraceElement)
					.forEach(builder::addStackTrace);
			if (e.getMessage() != null)
				builder.setMessage(e.getMessage());
			return builder.build();
		});
	}
}
