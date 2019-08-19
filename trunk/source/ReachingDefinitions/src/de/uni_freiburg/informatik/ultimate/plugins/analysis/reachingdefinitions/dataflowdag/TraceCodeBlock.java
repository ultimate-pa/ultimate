/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class TraceCodeBlock {

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mBlock == null) ? 0 : mBlock.hashCode());
		result = prime * result + mIndex;
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
		final TraceCodeBlock other = (TraceCodeBlock) obj;
		if (mBlock == null) {
			if (other.mBlock != null) {
				return false;
			}
		} else if (!mBlock.equals(other.mBlock)) {
			return false;
		}
		return mIndex == other.mIndex;
	}

	private final List<CodeBlock> mTrace;
	private final CodeBlock mBlock;
	private final int mIndex;
	
	private IPredicate mInterpolant;

	public TraceCodeBlock(final List<CodeBlock> trace, final CodeBlock block, final int index) {
		mTrace = trace;
		mBlock = block;
		mIndex = index;
	}

	public List<CodeBlock> getTrace() {
		return mTrace;
	}

	public CodeBlock getBlock() {
		return mBlock;
	}

	public int getIndex() {
		return mIndex;
	}
	
	public void addInterpolant(final IPredicate interpolant) {
		mInterpolant = interpolant;
	}
	
	public IPredicate getInterpolant() {
		return mInterpolant;
	}

	@Override
	public String toString() {
		return "[" + mIndex + "] " + mBlock.toString()
				+ (mInterpolant == null ? "" : " itp: " + mInterpolant);
	}
}
