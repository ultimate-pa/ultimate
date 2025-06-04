package de.uni_freiburg.informatik.ultimate.core.lib.results.convert;

import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.SarifDTOMapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.SimpleDTOMapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifDTO;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple.SimpleDTO;
import de.uni_freiburg.informatik.ultimate.core.lib.serialize.JsonSerializer;
import de.uni_freiburg.informatik.ultimate.core.lib.serialize.YamlSerializer;

public final class ResultConverterFactory {

	public static IResultConverter create(final ResultOutputFormat format) {
		return switch (format) {
		case JSON -> new ResultConverter<>(new SimpleDTOMapper(), new JsonSerializer<SimpleDTO>());
		case YAML -> new ResultConverter<>(new SimpleDTOMapper(), new YamlSerializer<SimpleDTO>());
		case SARIF -> new ResultConverter<>(new SarifDTOMapper(), new JsonSerializer<SarifDTO>());
		};
	}
}
