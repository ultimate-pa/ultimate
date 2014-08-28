package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class TraceCodeBlock {

	private final List<CodeBlock> mTrace;
	private final CodeBlock mBlock;
	private final int mIndex;

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

	@Override
	public String toString() {
		return "[" + mIndex + "] " + mBlock.toString();
	}
}
