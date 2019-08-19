/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugRCFGVisitor extends SimpleRCFGVisitor {

	private int mPathCount;
	private int mNodeCount;
	private int mEdgeCount;
	private StringBuilder mStringBuilder;
	public final int mLimit;

	public DebugRCFGVisitor(ILogger logger, int limit) {
		super(logger);
		mPathCount = 0;
		mNodeCount = 0;
		mEdgeCount = 0;
		mStringBuilder = new StringBuilder();
		mLimit = limit;
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
		super.init(modelType, currentModelIndex, numberOfModels);
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
		mLogger.debug(mStringBuilder);
	}

	@Override
	public void pre(IcfgEdge edge) {
		++mEdgeCount;
		if (edge instanceof RootEdge) {
			mStringBuilder.append("RootEdge");
		} else {
			mStringBuilder.append(((CodeBlock) edge).getPrettyPrintedStatements());
		}
	}

	@Override
	public void pre(IcfgLocation node) {
		++mNodeCount;
		mStringBuilder.append(" --> ");
		mStringBuilder.append(node.toString());
		mStringBuilder.append(" --> ");
	}

	@Override
	public void endOfTrace() {
		++mPathCount;
		mStringBuilder.replace(mStringBuilder.length() - 5, mStringBuilder.length(), "");
		mStringBuilder.append("\n--\n");
	}

	@Override
	public boolean abortCurrentBranch() {
		return false;
	}

	@Override
	public boolean abortAll() {
		if ((mPathCount > mLimit || mNodeCount > mLimit || mEdgeCount > mLimit)) {
			mLogger.debug("Aborting debug session because node, path or edge limit was reached");
			return true;
		}
		return false;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
