package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.Objects;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

public class Location implements IYamlProvider {

	private final String mFileName;
	private final String mFileHash;
	private final int mLine;
	private final int mColumn;
	private final String mFunction;

	public Location(final String fileName, final String fileHash, final int line, final int column,
			final String function) {
		mFileName = fileName;
		mFileHash = fileHash;
		mLine = line;
		mColumn = column;
		mFunction = function;
	}

	public String getFileName() {
		return mFileName;
	}

	public String getFileHash() {
		return mFileHash;
	}

	public int getLine() {
		return mLine;
	}

	public int getColumn() {
		return mColumn;
	}

	public String getFunction() {
		return mFunction;
	}

	@Override
	public String toString() {
		return "(" + mLine + ", " + mColumn + ")";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mColumn, mFileHash, mFileName, mFunction, mLine);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final Location other = (Location) obj;
		return mColumn == other.mColumn && Objects.equals(mFileHash, other.mFileHash)
				&& Objects.equals(mFileName, other.mFileName) && Objects.equals(mFunction, other.mFunction)
				&& mLine == other.mLine;
	}

	@Override
	public YamlNode toYaml() {
		return Yaml.createYamlMappingBuilder().add("file_name", mFileName).add("file_has", mFileHash)
				.add("line", Integer.toString(mLine)).add("column", Integer.toString(mColumn))
				.add("function", mFunction).build();
	}
}
