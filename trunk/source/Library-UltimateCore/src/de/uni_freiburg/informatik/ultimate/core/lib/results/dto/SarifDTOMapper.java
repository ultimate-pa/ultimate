package de.uni_freiburg.informatik.ultimate.core.lib.results.dto;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifDTO;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public final class SarifDTOMapper implements IResultDTOMapper<SarifDTO> {

	@Override
	public SarifDTO transform(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results) {
		throw new UnsupportedOperationException("Not implemented yet!");
	}
}
