/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.io.Serializable;
import java.util.Arrays;

public class BoogieTypeConstructor implements Serializable{
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 4794962965656111904L;
	private final String name;
	private final boolean isFinite;
	private final int    paramCount;
	private final int[]  paramOrder;
	private final BoogieType synonym;

	public BoogieTypeConstructor(final String name, final boolean isFinite, final int paramCount, final int[] paramOrder) {
		this(name, isFinite, paramCount, paramOrder, null);
	}
	public BoogieTypeConstructor(final String name, final boolean isFinite, final int paramCount, final int[] paramOrder, final BoogieType synonym) {
		this.name = name;
		this.isFinite = isFinite;
		this.paramCount = paramCount;
		this.paramOrder = paramOrder;
		this.synonym = synonym;
	}

	public String getName() {
		return name;
	}
	public int getParamCount() {
		return paramCount;
	}
	public int[] getParamOrder() {
		return paramOrder;
	}
	public BoogieType getSynonym() {
		return synonym;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(name);
		if (paramOrder.length > 0) {
			sb.append('<');
			String comma = "";
			for (int i = 0; i < paramOrder.length; i++) {
				sb.append(comma).append(paramOrder[i]);
				comma = ",";
			}
			sb.append('>');
		}
		if (synonym != null) {
			sb.append('=').append(synonym);
		}
		return sb.toString();
	}

	public boolean isFinite() {
		return isFinite;
	}
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (isFinite ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + paramCount;
		result = prime * result + Arrays.hashCode(paramOrder);
		result = prime * result + ((synonym == null) ? 0 : synonym.hashCode());
		return result;
	}
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final BoogieTypeConstructor other = (BoogieTypeConstructor) obj;
		if (isFinite != other.isFinite) {
			return false;
		}
		if (name == null) {
			if (other.name != null) {
				return false;
			}
		} else if (!name.equals(other.name)) {
			return false;
		}
		if (paramCount != other.paramCount) {
			return false;
		}
		if (!Arrays.equals(paramOrder, other.paramOrder)) {
			return false;
		}
		if (synonym == null) {
			if (other.synonym != null) {
				return false;
			}
		} else if (!synonym.equals(other.synonym)) {
			return false;
		}
		return true;
	}

}
