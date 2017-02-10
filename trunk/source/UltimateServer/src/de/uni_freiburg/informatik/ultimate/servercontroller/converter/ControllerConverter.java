package de.uni_freiburg.informatik.ultimate.servercontroller.converter;

import java.util.Arrays;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.Converter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ResultSummary;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolChainResult;

public class ControllerConverter extends Converter<GeneratedMessageV3, Object> {
	public static ControllerConverter get() {
		return new ControllerConverter(null);
	}
	
	protected ControllerConverter(IToolchainStorage storage) {
		super(Object.class, storage);
	}

	private static Controller.StackTraceElement convertStackTraceElement(StackTraceElement el) {
		return Controller.StackTraceElement.newBuilder().setDeclaringClass(el.getClassName())
				.setFileName(el.getFileName()).setMethodName(el.getMethodName()).setLineNumber(el.getLineNumber())
				.build();
	}

	@Override
	protected void init(ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(ResultSummary.class, ResultSummarizer.class, rs -> {
			return ResultSummary.newBuilder().setDescription(rs.getResultDescription())
					.setResult(ToolChainResult.valueOf(rs.getResultSummary().toString())).build();
		});

		converterRegistry.registerBA(Controller.Exception.class, Throwable.class, e -> {
			final Controller.Exception.Builder builder = Controller.Exception.newBuilder()
					.setClass_(e.getClass().getName()).setMessage(e.getMessage());
			Arrays.stream(e.getStackTrace()).map(ControllerConverter::convertStackTraceElement)
					.forEach(builder::addStackTrace);
			return builder.build();
		});
	}
}
