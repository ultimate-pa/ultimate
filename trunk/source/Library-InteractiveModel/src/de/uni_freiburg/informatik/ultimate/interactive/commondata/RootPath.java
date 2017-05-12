package de.uni_freiburg.informatik.ultimate.interactive.commondata;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.DirectoryStream.Filter;
import java.nio.file.Files;
import java.nio.file.Path;

public class RootPath {
	public final PathFilter mFilter;
	public final Path mBase;
	public final String mTag;

	private RootPath(final Path base, final String tag, final PathFilter filter) {
		mBase = base;
		mTag = tag;
		mFilter = filter;
	}

	public static RootPath newInstance(final Path base, final String tag) {
		return new RootPath(base, tag, Files::newDirectoryStream);
	}

	public static RootPath newInstance(final Path base, final String tag, final Filter<? super Path> filter) {
		return new RootPath(base, tag, p -> Files.newDirectoryStream(p, filter));
	}

	public static RootPath newInstance(final Path base, final String tag, final String filter) {
		return new RootPath(base, tag, p -> Files.newDirectoryStream(p, filter));
	}

	@FunctionalInterface
	public interface PathFilter {
		DirectoryStream<Path> apply(Path path) throws IOException;
	}
}
