package de.uni_freiburg.informatik.ultimate.interactive.common;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.function.Consumer;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.common.protobuf.Common;
import de.uni_freiburg.informatik.ultimate.interactive.common.protobuf.Common.Choice.Request;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.ChoiceRequest;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.RootPath;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.RootPath.PathFilter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.AbstractConverter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientCrazyException;

public class Converter extends AbstractConverter<GeneratedMessageV3, Object> {
	public Converter(final ILogger logger) {
		super(logger, Object.class);
	}

	public Converter(final IUltimateServiceProvider services) {
		super(services, Object.class);
	}

	private static Common.StackTraceElement convertStackTraceElement(final StackTraceElement stackTraceEl) {
		return Common.StackTraceElement.newBuilder().setDeclaringClass(stackTraceEl.getClassName())
				.setFileName(stackTraceEl.getFileName()).setMethodName(stackTraceEl.getMethodName())
				.setLineNumber(stackTraceEl.getLineNumber()).build();
	}

	private Common.File convertFile(final java.io.File file) {
		final Common.File.Builder builder = Common.File.newBuilder();
		builder.setFileName(file.getName());

		final Path path = Paths.get(file.getAbsolutePath());
		try {
			final String content = new String(Files.readAllBytes(path));
			builder.setContent(content);
		} catch (final IOException e) {
			getLogger().error(e);
		}

		return builder.build();
	}

	private static Common.FS.Path convertPath(final Path path) {
		final Common.FS.Path.Builder builder = Common.FS.Path.newBuilder();
		path.forEach(p -> builder.addPiece(p.toString()));
		return builder.build();
	}

	private static Path fromPath(final String base, final Common.FS.Path path) {
		return Paths.get(base, path.getPieceList().toArray(new String[path.getPieceCount()]));
	}

	private static Path[] toPaths(final Common.FS.Paths paths) {
		final Path[] result = new Path[paths.getPathsCount()];
		for (int i = 0; i < paths.getPathsCount(); i++) {
			final Common.FS.Path path = paths.getPaths(i);
			result[i] = Paths.get(path.getPiece(0), path.getPieceList().stream().skip(1).toArray(String[]::new));
		}
		return result;
	}

	private Common.FS.Directory convertDirectory(final Path path, final PathFilter filter) {
		if (!path.toFile().isDirectory())
			throw new IllegalArgumentException(path.toString() + " is not a valid directory.");
		final Common.FS.Directory.Builder builder = Common.FS.Directory.newBuilder();
		builder.setName(path.getFileName().toString());
		try {
			filter.apply(path).forEach(p -> {
				final File file = p.toFile();
				if (file.isFile()) {
					builder.addFiles(file.getName());
				} else {
					final Common.FS.Directory dir = convertDirectory(p, filter);
					builder.addSubdirectory(dir);
				}
			});
		} catch (final IOException e) {
			getLogger().error(e);
		}
		return builder.build();
	}

	private Common.FS convertBasePath(final RootPath path) {
		final Common.FS.Builder builder = Common.FS.newBuilder();
		builder.setBase(convertDirectory(path.mBase, path.mFilter));
		builder.setTag(path.mTag);
		return builder.build();
	}

	private static Boolean toBoolean(final Common.Confirm confirm) {
		return confirm.getOk();
	}

	@SuppressWarnings("unchecked")
	private static Request convertChoiceRequest(final ChoiceRequest available) {
		final Request.Builder builder = Request.newBuilder();
		available.mChoices.stream().map(available.mToString).forEach((Consumer<String>) builder::addChoice);
		if (available.mTitle != null)
			builder.setTitle(available.mTitle);
		if (available.mSubTitle != null)
			builder.setSubtitle(available.mSubTitle);
		return builder.build();
	}

	private static Object getChoice(final Common.Choice choice, final ChoiceRequest available) {
		final int choiceid = choice.getIndex();
		if (choiceid < 0 || choiceid > available.mChoices.size()) {
			throw new ClientCrazyException(String.format("Choice index from Client not within bounds: %1$d", choiceid));
		}
		return available.mChoices.get(choiceid);
	}

	private static Common.Message fromMessage(final String message) {
		final String[] msgs = message.split(":");
		final String text = msgs.length > 0 ? msgs[msgs.length - 1] : "Empty Message";
		final String title = msgs.length > 1 ? msgs[0] : "Message";
		final String subtitle = msgs.length > 2 ? msgs[1] : "";

		return Common.Message.newBuilder().setTitle(title).setSubtitle(subtitle).setText(text).build();
	}

	@Override
	protected void init(final ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(Common.Exception.class, Throwable.class, e -> {
			final Common.Exception.Builder builder = Common.Exception.newBuilder().setClass_(e.getClass().getName());
			Arrays.stream(e.getStackTrace()).map(Converter::convertStackTraceElement).forEach(builder::addStackTrace);
			if (e.getMessage() != null)
				builder.setMessage(e.getMessage());
			return builder.build();
		});

		converterRegistry.registerBA(Common.File.class, java.io.File.class, this::convertFile);

		converterRegistry.registerBA(Common.FS.class, RootPath.class, this::convertBasePath);

		converterRegistry.registerBA(Common.FS.Path.class, Path.class, Converter::convertPath);

		converterRegistry.registerAB(Common.FS.Paths.class, Path[].class, Converter::toPaths);

		converterRegistry.registerAB(Common.Confirm.class, Boolean.class, Converter::toBoolean);

		converterRegistry.registerBA(Common.Message.class, String.class, Converter::fromMessage);

		converterRegistry.registerBA(Common.Choice.Request.class, ChoiceRequest.class, Converter::convertChoiceRequest);

		converterRegistry.registerRConv(Common.Choice.class, ChoiceRequest.class, Object.class, Converter::getChoice);

		converterRegistry.registerRConv(Common.FS.Path.class, RootPath.class, Path.class, Converter::getPath);

	}

	private static Path getPath(final Common.FS.Path path, final RootPath base) {
		return fromPath(base.mBase.toString(), path);
	}
}