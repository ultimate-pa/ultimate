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
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.EnumSet;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
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
	private final String mInputFilename;

	private final PatternType[] mReqs;

	public ReqCheck(final Check.Spec type, final int[] reqNrs, final PatternType[] reqs, final String inputFilename) {
		this(EnumSet.of(type), reqNrs, reqs, inputFilename);
	}

	private ReqCheck(final EnumSet<Check.Spec> types, final int[] reqNrs, final PatternType[] reqs,
			final String inputFilename) {
		this(types, reqNrs[0] + 1, reqNrs[reqNrs.length - 1] + 1, reqs, inputFilename);
	}

	private ReqCheck(final EnumSet<Check.Spec> types, final int startline, final int endline, final PatternType[] reqs,
			final String inputFilename) {
		super(types, a -> ReqCheck.getCustomPositiveMessage(a, reqs), a -> ReqCheck.getCustomNegativeMessage(a, reqs));
		mStartline = startline;
		mEndline = endline;
		mInputFilename = inputFilename;
		mReqs = reqs;
	}

	public int getStartLine() {
		return mStartline;
	}

	public int getEndLine() {
		return mEndline;
	}

	public String getFileName() {
		return mInputFilename;
	}

	private static String getCustomPositiveMessage(final Spec spec, final PatternType[] types) {
		return getRequirementTexts(types) + " " + getPositiveMessage(spec);
	}

	private static String getCustomNegativeMessage(final Spec spec, final PatternType[] types) {
		return getRequirementTexts(types) + " " + getNegativeMessage(spec);
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

	public ReqCheck merge(final ReqCheck other) {
		if (other == null) {
			return this;
		}
		if (!other.mInputFilename.equals(mInputFilename)) {
			throw new UnmergeableAnnotationsException(this, other);
		}

		final EnumSet<Spec> newSpec = EnumSet.copyOf(getSpec());
		newSpec.addAll(other.getSpec());
		final int startline = Math.min(mStartline, other.mStartline);
		final int endline = Math.max(mEndline, other.mEndline);
		final PatternType[] reqs = DataStructureUtils.concat(mReqs, other.mReqs);
		return new ReqCheck(newSpec, startline, endline, reqs, mInputFilename);
	}

}
