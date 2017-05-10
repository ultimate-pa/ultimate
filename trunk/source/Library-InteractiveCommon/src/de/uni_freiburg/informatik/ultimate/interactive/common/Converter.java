package de.uni_freiburg.informatik.ultimate.interactive.common;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.common.protobuf.Common;
import de.uni_freiburg.informatik.ultimate.interactive.common.protobuf.Common.Choice.Request;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.ChoiceRequest;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.AbstractConverter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientCrazyException;

public class Converter extends AbstractConverter<GeneratedMessageV3, Object> {
	public Converter(final ILogger logger) {
		super(logger, Object.class);
	}
	
	public Converter(IUltimateServiceProvider services) {
		super(services, Object.class);
	}

	private static Common.StackTraceElement convertStackTraceElement(StackTraceElement el) {
		return Common.StackTraceElement.newBuilder().setDeclaringClass(el.getClassName()).setFileName(el.getFileName())
				.setMethodName(el.getMethodName()).setLineNumber(el.getLineNumber()).build();
	}

	private static Common.File convertFile(final java.io.File file) {
		final Common.File.Builder builder = Common.File.newBuilder();
		builder.setFileName(file.getName());

		Path path = Paths.get(file.getAbsolutePath());
		try {
			final String content = new String(Files.readAllBytes(path));
			builder.setContent(content);
		} catch (IOException e) {
		}

		return builder.build();
	}

	private static Boolean toBoolean(final Common.Confirm confirm) {
		return confirm.getOk();
	}

	private static Request convertChoiceRequest(final ChoiceRequest available) {
		final Request.Builder builder = Request.newBuilder();
		available.mChoices.stream().map(available.mToString).forEach(s -> builder.addChoice((String) s));
		return builder.build();
	}

	private static Object getChoice(Common.Choice choice, final ChoiceRequest available) {
		final int choiceid = choice.getIndex();
		if (choiceid < 0 || choiceid > available.mChoices.size()) {
			throw new ClientCrazyException(String.format("Choice index from Client not within bounds: %1$d", choiceid));
		}
		return available.mChoices.get(choiceid);
	}

	@Override
	protected void init(ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(Common.Exception.class, Throwable.class, e -> {
			final Common.Exception.Builder builder = Common.Exception.newBuilder().setClass_(e.getClass().getName());
			Arrays.stream(e.getStackTrace()).map(Converter::convertStackTraceElement).forEach(builder::addStackTrace);
			if (e.getMessage() != null)
				builder.setMessage(e.getMessage());
			return builder.build();
		});

		converterRegistry.registerBA(Common.File.class, java.io.File.class, Converter::convertFile);

		converterRegistry.registerAB(Common.Confirm.class, Boolean.class, Converter::toBoolean);

		converterRegistry.registerBA(Common.Choice.Request.class, ChoiceRequest.class, Converter::convertChoiceRequest);

		converterRegistry.registerRConv(Common.Choice.class, ChoiceRequest.class, Object.class, Converter::getChoice);
		;
	}
}