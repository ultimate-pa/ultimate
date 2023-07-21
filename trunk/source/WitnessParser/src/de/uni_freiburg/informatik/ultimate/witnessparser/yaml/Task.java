package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.List;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class Task implements IYamlProvider {
	private final List<String> mInputFiles;
	private final List<String> mInputFileHashes;
	private final String mSpecification;
	private final String mDataModel;
	private final String mLanguage;

	public Task(final List<String> inputFiles, final List<String> inputFileHashes, final String specification,
			final String dataModel, final String language) {
		mInputFiles = inputFiles;
		mInputFileHashes = inputFileHashes;
		mSpecification = specification;
		mDataModel = dataModel;
		mLanguage = language;
	}

	private static YamlNode fromList(final List<String> list) {
		final var builder = Yaml.createMutableYamlSequenceBuilder();
		list.forEach(builder::add);
		return builder.build();
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("input_files", fromList(mInputFiles))
				.add("input_file_hashes", fromList(mInputFileHashes)).add("specification", mSpecification)
				.add("data_model", mDataModel).add("language", mLanguage).build();
	}
}
