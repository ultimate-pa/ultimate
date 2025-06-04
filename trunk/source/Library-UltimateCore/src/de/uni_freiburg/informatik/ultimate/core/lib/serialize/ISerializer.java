package de.uni_freiburg.informatik.ultimate.core.lib.serialize;

import java.io.IOException;
import java.io.Writer;

public interface ISerializer<T> {

	String serialize(final T dto);

	default void write(final T dto, final Writer writer) throws IOException {
		writer.write(serialize(dto));
	}
}
