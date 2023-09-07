/*
 * Copyright (C) 2023 Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

import java.util.Objects;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlNode;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
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
		return "(" + mFileName + ", L" + mLine + "-" + mColumn + ")";
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
		return Yaml.createYamlMappingBuilder().add("file_name", mFileName).add("file_hash", mFileHash)
				.add("line", Integer.toString(mLine)).add("column", Integer.toString(mColumn))
				.add("function", mFunction).build();
	}
}
