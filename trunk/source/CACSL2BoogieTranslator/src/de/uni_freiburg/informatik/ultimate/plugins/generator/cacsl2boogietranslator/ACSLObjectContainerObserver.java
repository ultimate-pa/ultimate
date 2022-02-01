/*
 * Copyright (C) 2016 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

public class ACSLObjectContainerObserver implements IUnmanagedObserver {

	private ACSLNode mAnotation;
	private boolean mListen;
	private final ILogger mLogger;
	private boolean mWaitForMe;

	public ACSLObjectContainerObserver(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels)
			throws Throwable {
		mWaitForMe = currentModelIndex < numberOfModels - 1;
		if ("de.uni_freiburg.informatik.ultimate.ltl2aut".equals(modelType.getCreator())) {
			mLogger.info("Executing ACSLObjectContainerObserver...");
			mListen = true;
		} else {
			mListen = false;
		}
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	public ACSLNode getAnnotation() {
		return mAnotation;
	}

	public boolean waitForMe() {
		return mWaitForMe && mAnotation == null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!mListen) {
			return false;
		}
		if (root instanceof ObjectContainer && ((ObjectContainer<?>) root).getValue() instanceof ACSLNode) {
			final ObjectContainer<?> container = (ObjectContainer<?>) root;
			mAnotation = (ACSLNode) container.getValue();
		}
		return false;
	}

}
