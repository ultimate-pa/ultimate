package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class Invariant implements IYamlProvider {

	private final String mExpression;
	private final String mType;
	private final String mFormat;

	public Invariant(final String expression, final String type, final String format) {
		mExpression = expression;
		mType = type;
		mFormat = format;
	}

	public String getExpression() {
		return mExpression;
	}

	public String getType() {
		return mType;
	}

	public String getFormat() {
		return mFormat;
	}

	@Override
	public String toString() {
		return mExpression;
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("string", mExpression).add("type", mType).add("format", mFormat)
				.build();
	}
}
