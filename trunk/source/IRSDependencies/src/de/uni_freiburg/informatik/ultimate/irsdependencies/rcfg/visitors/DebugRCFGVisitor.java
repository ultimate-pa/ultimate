package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugRCFGVisitor extends SimpleRCFGVisitor {

	private static Logger sLogger = UltimateServices.getInstance()
			.getLogger(Activator.PLUGIN_ID);

	private int mPathCount;
	private int mNodeCount;
	private int mEdgeCount;
	private StringBuilder mStringBuilder;
	public final int mLimit;

	public DebugRCFGVisitor(int limit) {
		mPathCount = 0;
		mNodeCount = 0;
		mEdgeCount = 0;
		mStringBuilder = new StringBuilder();
		mLimit = limit;
	}

	@Override
	public void init() {
		super.init();
		mPathCount = 0;
		mNodeCount = 0;
		mEdgeCount = 0;
		mStringBuilder = new StringBuilder();
		mStringBuilder.append("\n--\n");
	}

	@Override
	public void finish() {
		super.finish();
		mStringBuilder.append("===============");
		mStringBuilder.append("\nPathCount: " + mPathCount);
		mStringBuilder.append("\nNodeCount: " + mNodeCount);
		mStringBuilder.append("\nEdgeCount: " + mEdgeCount);
		mStringBuilder.append("\nLimit: " + mLimit);
		mStringBuilder.append("\n===============");
		sLogger.debug(mStringBuilder);
	}

	@Override
	public void pre(RCFGEdge edge) {
		++mEdgeCount;
		if (edge instanceof RootEdge) {
			mStringBuilder.append("RootEdge");
		} else {
			mStringBuilder.append(((CodeBlock) edge)
					.getPrettyPrintedStatements());
		}
	}

	@Override
	public void pre(RCFGNode node) {
		++mNodeCount;
		mStringBuilder.append(" --> ");
		mStringBuilder.append(node.toString());
		mStringBuilder.append(" --> ");
	}

	public void endOfTrace() {
		++mPathCount;
		mStringBuilder.replace(mStringBuilder.length() - 5,
				mStringBuilder.length(), "");
		mStringBuilder.append("\n--\n");
	}

	public boolean abortCurrentBranch() {
		return false;
	}

	public boolean abortAll() {
		if ((mPathCount > mLimit || mNodeCount > mLimit || mEdgeCount > mLimit)) {
			sLogger.debug("Aborting debug session because node, path or edge limit was reached");
			return true;
		}
		return false;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
