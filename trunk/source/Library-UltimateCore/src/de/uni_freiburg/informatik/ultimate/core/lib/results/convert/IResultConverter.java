package de.uni_freiburg.informatik.ultimate.core.lib.results.convert;

import java.io.IOException;
import java.io.Writer;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public interface IResultConverter {

	String convert(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results);

	default void write(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results, final Writer writer) throws IOException {
		writer.write(convert(toolchain, core, results));
	}
}
