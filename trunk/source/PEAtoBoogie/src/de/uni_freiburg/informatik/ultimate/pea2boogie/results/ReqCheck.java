/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReqCheck extends Check {

	private static final long serialVersionUID = 6800618860906443122L;

	private final int mStartline;
	private final int mEndline;

	private final String[] mReqIds;

	private final String[] mPeaNames;
	
	private final String mMessage;

	public ReqCheck(final Check.Spec type) {
		this(EnumSet.of(type), 0, 0, new String[0], new String[0], "");
	}

	public ReqCheck(final Check.Spec type, final String[] reqIds, final String[] peaNames, String message) {
		this(EnumSet.of(type), reqIds, peaNames, message);
	}
	
	public ReqCheck(final Check.Spec type, final String[] reqIds, final String[] peaNames) {
		this(EnumSet.of(type), reqIds, peaNames, "");
	}

	private ReqCheck(final EnumSet<Check.Spec> types, final String[] reqIds, final String[] peaNames, String message) {
		this(types, -1, -1, reqIds, peaNames, message);
	}

	private ReqCheck(final EnumSet<Check.Spec> types, final int startline, final int endline, final String[] reqIds,
			final String[] peaNames, String message) {
		super(types, a -> ReqCheck.getCustomPositiveMessage(a, reqIds, peaNames),
				a -> ReqCheck.getCustomNegativeMessage(a, reqIds, peaNames));
		mStartline = startline;
		mEndline = endline;
		mReqIds = reqIds;
		mPeaNames = peaNames;
		mMessage = message;
	}

	public int getStartLine() {
		return mStartline;
	}

	public int getEndLine() {
		return mEndline;
	}

	private static String getCustomPositiveMessage(final Spec spec, final String[] reqIds, final String[] peaNames) {
		return getRequirementTexts(reqIds, peaNames) + " " + getDefaultPositiveMessage(spec);
	}

	private static String getCustomNegativeMessage(final Spec spec, final String[] reqIds, final String[] peaNames) {
		return getRequirementTexts(reqIds, peaNames) + " " + getDefaultNegativeMessage(spec);
	}

	private static String getRequirementTexts(final String[] reqIds, final String[] peaNames) {
		if (reqIds.length == 0) {
			return "All requirements are";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Requirement");
		if (reqIds.length != 1) {
			sb.append("s");
		}
		final Iterator<String> iter = Arrays.stream(reqIds).iterator();
		sb.append(" ").append(iter.next());
		while (iter.hasNext()) {
			sb.append(", ").append(iter.next());
		}
		if (reqIds.length != 1) {
			sb.append(" are");
		} else {
			sb.append(" is");
		}
		return sb.toString();
	}

	public ReqCheck merge(final ReqCheck other) {
		if (other == null) {
			return this;
		}
		if (other == this) {
			return this;
		}

		final EnumSet<Spec> newSpec = EnumSet.copyOf(getSpec());
		newSpec.addAll(other.getSpec());
		final int startline = Math.min(mStartline, other.mStartline);
		final int endline = Math.max(mEndline, other.mEndline);
		final String[] reqIds = DataStructureUtils.concat(mReqIds, other.mReqIds);
		final String[] peaNames = DataStructureUtils.concat(mPeaNames, other.mPeaNames);
		final String message = mMessage.concat(other.getMessage());
		return new ReqCheck(newSpec, startline, endline, reqIds, peaNames, message);
	}
	
	private String createMessage() {
		if(mMessage.isEmpty()) {
			return "";
		}
		return mMessage;
	}

	public Set<String> getReqIds() {
		return new LinkedHashSet<>(Arrays.asList(mReqIds));
	}

	public Set<String> getPeaNames() {
		return new LinkedHashSet<>(Arrays.asList(mPeaNames));
	}
	
	public String getMessage( ) {
		return mMessage;
	}

	@Override
	public String toString() {
		if (mReqIds.length == 0) {
			return super.toString() + " for all requirements";
		}
		return super.toString() + " for " + Arrays.stream(mReqIds).collect(Collectors.joining(", ")) + " " + createMessage();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + mEndline;
		result = prime * result + Arrays.hashCode(mReqIds);
		result = prime * result + Arrays.hashCode(mPeaNames);
		result = prime * result + mMessage.hashCode();
		result = prime * result + mStartline;
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ReqCheck other = (ReqCheck) obj;
		if (mStartline != other.mStartline) {
			return false;
		}
		if (mEndline != other.mEndline) {
			return false;
		}
		if (!Arrays.equals(mReqIds, other.mReqIds)) {
			return false;
		}
		if (!Arrays.equals(mPeaNames, other.mPeaNames)) {
			return false;
		}
		if(!mMessage.equalsIgnoreCase(other.getMessage())) {
			return false;
		}
		return true;
	}

}
