/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie;

import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.ParseTreeElementWrapper;

public class LlvmirToBoogieObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private WrapperNode mRootNode;

	public LlvmirToBoogieObserver(final IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels)
			throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof ParseTreeElementWrapper)) {
			mLogger.error("Expected ParseTreeElementWrapper, but got " + root.getClass().getSimpleName());
			return false;
		}

		final ParseTreeElementWrapper parseTreeElementWrapper = (ParseTreeElementWrapper) root;
		final ParseTree tree = parseTreeElementWrapper.getParseTree();

		final LlvmirToBoogieListener listener = new LlvmirToBoogieListener(mServices, mLogger, mRootNode);
		ParseTreeWalker.DEFAULT.walk(listener, tree);
		mRootNode = listener.getResult();

		mLogger.info("Successfully processed the LLVM IR parse tree.");
		return false;
	}

	public IElement getRoot() {
		return mRootNode;
	}
}
