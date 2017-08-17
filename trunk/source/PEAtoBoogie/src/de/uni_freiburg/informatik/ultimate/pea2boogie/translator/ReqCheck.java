/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class ReqCheck extends Check {

	private static final long serialVersionUID = 6800618860906443122L;

	enum ReqSpec {
		RTINCONSISTENT, VACUOUS, INCOMPLETE, UNKNOWN, CONSISTENCY
	}

	private final int mStartline;
	private final int mEndline;
	private final String mPositive;
	private final String mNegative;
	private final String mInputFilename;

	public ReqCheck(final ReqSpec type, final int[] reqNrs, final PatternType[] reqs, final String inputFilename) {
		super(Check.Spec.UNKNOWN);
		assert reqNrs != null && reqNrs.length > 0;
		assert reqs != null && reqs.length > 0;
		mStartline = reqNrs[0] + 1;
		mEndline = reqNrs[reqNrs.length - 1] + 1;
		mInputFilename = inputFilename;
		mPositive = createPositiveMessage(type, reqs);
		mNegative = createNegativeMessage(type, reqs);
	}

	public int getStartLine() {
		return mStartline;
	}

	public int getEndLine() {
		return mEndline;
	}

	private static String createPositiveMessage(final ReqSpec spec, final PatternType[] types) {
		switch (spec) {
		case RTINCONSISTENT:
			assert types.length > 1;
			return getRequirementTexts(types) + " rt-consistent";
		case VACUOUS:
			assert types.length == 1;
			return getRequirementTexts(types) + " vacuous.";
		case CONSISTENCY:
			return getRequirementTexts(types) + " inconsistent";
		case INCOMPLETE:
		case UNKNOWN:
		default:
			return "Unknown Check";
		}
	}

	private static String createNegativeMessage(final ReqSpec spec, final PatternType[] types) {
		switch (spec) {
		case RTINCONSISTENT:
			assert types.length > 1;
			return getRequirementTexts(types) + " rt-inconsistent";
		case VACUOUS:
			assert types.length == 1;
			return getRequirementTexts(types) + " non-vacuous.";
		case CONSISTENCY:
			return getRequirementTexts(types) + " consistent";
		case INCOMPLETE:
		case UNKNOWN:
		default:
			return "Unknown Check";
		}
	}

	private static String getRequirementTexts(final PatternType[] types) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Requirement");
		if (types.length != 1) {
			sb.append("s");
		}
		for (final PatternType type : types) {
			sb.append(" ").append(type.getId());
		}
		if (types.length != 1) {
			sb.append(" are");
		} else {
			sb.append(" is");
		}
		return sb.toString();
	}

	@Override
	public String getPositiveMessage() {
		return mPositive;
	}

	@Override
	public String getNegativeMessage() {
		return mNegative;
	}

	public String getFileName() {
		return mInputFilename;
	}
}
