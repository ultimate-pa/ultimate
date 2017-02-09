package de.uni_freiburg.informatik.ultimate.servercontroller.converter;

import java.util.Arrays;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.interactive.ApplyConversionToInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ResultSummary;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.ToolChainResult;

public class ControllerConverter {
	private static ConverterRegistry<GeneratedMessageV3, Object> ProtoObjectConverter = new ConverterRegistry<>();

	private static Controller.StackTraceElement convertStackTraceElement(StackTraceElement el) {
		return Controller.StackTraceElement.newBuilder().setDeclaringClass(el.getClassName())
				.setFileName(el.getFileName()).setMethodName(el.getMethodName()).setLineNumber(el.getLineNumber())
				.build();
	}

	static {
		ProtoObjectConverter.registerBA(ResultSummary.class, ResultSummarizer.class, rs -> {
			return ResultSummary.newBuilder().setDescription(rs.getResultDescription())
					.setResult(ToolChainResult.valueOf(rs.getResultSummary().toString())).build();
		});

		ProtoObjectConverter.registerBA(Controller.Exception.class, Throwable.class, e -> {
			final Controller.Exception.Builder builder = Controller.Exception.newBuilder()
					.setClass_(e.getClass().getName()).setMessage(e.getMessage());
			Arrays.stream(e.getStackTrace()).map(ControllerConverter::convertStackTraceElement)
					.forEach(builder::addStackTrace);
			return builder.build();
		});

	}

	public static IInteractive<Object> get(IInteractive<GeneratedMessageV3> protoInterface,
			ITypeRegistry<GeneratedMessageV3> typeRegistry) {

		ProtoObjectConverter.registerATypes(typeRegistry);

		return new ApplyConversionToInteractive<>(protoInterface, ProtoObjectConverter, Object.class);
	}
}
