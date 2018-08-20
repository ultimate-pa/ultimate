/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 *
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.blockencoding.converter.MinModelConverter;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BlockEncodingObserver implements IUnmanagedObserver {

	private BoogieIcfgContainer mRoot;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public BlockEncodingObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public boolean process(final IElement root) {
		final BoogieIcfgContainer icfgContainer = (BoogieIcfgContainer) root;
		final RootNode artificialRoot = icfgContainer.constructRootNode();
		new BlockEncoder(mLogger, mServices).startMinimization(artificialRoot);
		final RootNode newRoot = new MinModelConverter(mServices).startConversion(artificialRoot);
		mRoot = makeContainerFromRoot(newRoot);
		return false;
	}

	private BoogieIcfgContainer makeContainerFromRoot(final RootNode newRoot) {
		final BoogieIcfgContainer rootAnnot = newRoot.getRootAnnot();
		final BoogieIcfgContainer container = new BoogieIcfgContainer(mServices,
				newRoot.getRootAnnot().getBoogieDeclarations(), newRoot.getRootAnnot().getBoogie2SMT(), null);
		// container.getProcedureEntryNodes().putAll(m);
		return newRoot.getRootAnnot();
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not required
	}

	@Override
	public void finish() {
		// not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getRoot() {
		return mRoot;
	}

}
