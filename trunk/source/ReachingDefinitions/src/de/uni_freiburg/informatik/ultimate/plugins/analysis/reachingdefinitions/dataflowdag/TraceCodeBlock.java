package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

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
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TraceCodeBlock other = (TraceCodeBlock) obj;
		if (mBlock == null) {
			if (other.mBlock != null)
				return false;
		} else if (!mBlock.equals(other.mBlock))
			return false;
		if (mIndex != other.mIndex)
			return false;
		return true;
	}

	private final List<CodeBlock> mTrace;
	private final CodeBlock mBlock;
	private final int mIndex;
	
	private IPredicate mInterpolant;

	public TraceCodeBlock(List<CodeBlock> trace, CodeBlock block, int index) {
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
	
	public void addInterpolant(IPredicate interpolant) {
		this.mInterpolant = interpolant;
	}
	
	public IPredicate getInterpolant() {
		return mInterpolant;
	}

	@Override
	public String toString() {
		return "[" + mIndex + "] " + mBlock.toString();
	}
}
