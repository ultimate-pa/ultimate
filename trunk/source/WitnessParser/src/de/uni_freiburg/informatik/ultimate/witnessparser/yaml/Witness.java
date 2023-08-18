package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.List;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;
import com.amihaiemil.eoyaml.YamlSequenceBuilder;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;

public class Witness extends BasePayloadContainer implements IYamlProvider {
	private static final long serialVersionUID = 2111530908758373549L;

	private final List<WitnessEntry> mEntries;

	public Witness(final List<WitnessEntry> entries) {
		mEntries = entries;
	}

	public List<WitnessEntry> getEntries() {
		return mEntries;
	}

	@Override
	public String toString() {
		return mEntries.toString();
	}

	@Override
	public YamlNode toYaml() {
		final YamlSequenceBuilder builder = Yaml.createMutableYamlSequenceBuilder();
		mEntries.forEach(x -> builder.add(x.toYaml()));
		return builder.build();
	}

	public String toYamlString() {
		return toYaml().toString() + "\n";
	}

	public boolean isCorrectnessWitness() {
		// TODO: Check this, when we also support violation witnesses
		return true;
	}
}
