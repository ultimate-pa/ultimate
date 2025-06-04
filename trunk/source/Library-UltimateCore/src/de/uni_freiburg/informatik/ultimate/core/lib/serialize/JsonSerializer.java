package de.uni_freiburg.informatik.ultimate.core.lib.serialize;

import java.io.IOException;
import java.io.Writer;

import com.google.gson.FieldNamingPolicy;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

/**
 * Result writer for JSON result data objects.
 *
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public final class JsonSerializer<T> implements ISerializer<T> {

	/**
	 * JSON serialization instance.
	 */
	private static final Gson WRITER = Builder().create();

	/**
	 * Return builder to create the YAML serialization instance.
	 *
	 * @return Builder for the YAML serialization instance.
	 */
	private static GsonBuilder Builder() {
		return new GsonBuilder().enableComplexMapKeySerialization().setPrettyPrinting()
				.setFieldNamingPolicy(FieldNamingPolicy.UPPER_CAMEL_CASE).setDateFormat("yyyy-MM-dd'T'HH:mm:ssX");
	}

	@Override
	public String serialize(final T dto) {
		return WRITER.toJson(dto);
	}

	@Override
	public void write(final T dto, final Writer writer) throws IOException {
		WRITER.toJson(dto, writer);
	}
}
