package de.uni_freiburg.informatik.ultimate.core.lib.results.convert;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.IResultDTOMapper;
import de.uni_freiburg.informatik.ultimate.core.lib.serialize.ISerializer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public final class ResultConverter<T> implements IResultConverter {

	private final IResultDTOMapper<T> mMapper;
	private final ISerializer<T> mSerializer;

	public ResultConverter(final IResultDTOMapper<T> mapper, final ISerializer<T> serializer) {
		mMapper = mapper;
		mSerializer = serializer;
	}

	@Override
	public String convert(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results) {
		return mSerializer.serialize(mMapper.transform(toolchain, core, results));
	}
}
