/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ChcToBoogie plug-in.
 *
 * The ChcToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ChcToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ChcToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ChcToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ChcToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornUtilConstants;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ChcToBoogieObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private Unit mResult;

	public ChcToBoogieObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mResult;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		final BasePayloadContainer rootNode = (BasePayloadContainer) root;

		final Map<String, IAnnotations> st = rootNode.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get(HornUtilConstants.HORN_ANNOT_NAME);
		mLogger.debug(annot.getAnnotationsAsMap().get(HornUtilConstants.HORN_ANNOT_NAME));

		return true;
	}
}
