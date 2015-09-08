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
package pea_to_boogie.translator;

import de.uni_freiburg.informatik.ultimate.result.Check;

public class ReqCheck extends Check {
	
	private static final long serialVersionUID = 6800618860906443122L;

	enum ReqSpec {
		RTINCONSISTENT,
		VACUOUS,
		INCOMPLETE,
		UNKNOWN
	}
	
	ReqSpec mType;
	int[] mReqNrs;
	Translator mTranslator;
	
	public ReqCheck(ReqSpec type, int[] reqNrs, Translator trans) {
		super(Check.Spec.UNKNOWN);
		this.mType = type;
		this.mReqNrs = reqNrs;
		this.mTranslator = trans;
	}
	
	public int getStartLine() {
		return mReqNrs[0]  + 1;
	}
	public int getEndLine() {
		return mReqNrs[mReqNrs.length-1]  + 1;
	}
	
	public String getPositiveMessage() {
		if (mType == ReqSpec.RTINCONSISTENT) {
			return "Some requirements are rt-consistent";
		} else if (mType == ReqSpec.VACUOUS){
			return "Requirement " + mTranslator.getRequirement(mReqNrs[0]) +
					   " is vacuous.";
		} else {
			return "Unknown Check";
		}
	}

	public String getNegativeMessage() {
		if (mType == ReqSpec.RTINCONSISTENT) {
			assert (mType == ReqSpec.RTINCONSISTENT);
			StringBuilder sb = new StringBuilder();
			sb.append("Requirement");
			if (mReqNrs.length != 1)
				sb.append("s");
			for (int nr : mReqNrs) {
				sb.append(" ").append(mTranslator.getRequirement(nr));
			}
			sb.append(" are rt-inconsistent");
			return sb.toString();
		} else if (mType == ReqSpec.VACUOUS){
			return "Requirement " + mTranslator.getRequirement(mReqNrs[0]) +
					   " is non-vacuous.";
		} else {
			return "Unknown Check";
		}
	}
	
	public String getFileName() {
		return mTranslator.getInputFilePath();
	}
}
