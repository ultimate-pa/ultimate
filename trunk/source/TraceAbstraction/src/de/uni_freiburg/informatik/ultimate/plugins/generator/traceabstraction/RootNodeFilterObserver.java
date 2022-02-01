/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;

/**
 * Observer that stores the root node of a model if this node has a given type.
 * 
 * @author Matthias Heizmann
 *
 * @param <E>
 *            Type of the root node that will be stored.
 */
public class RootNodeFilterObserver<E extends IElement> implements IUnmanagedObserver {
	private final Class<E> mRootNodeClass;
	private E mRootNode = null;

	public RootNodeFilterObserver(Class<E> rootNodeClass) {
		super();
		mRootNodeClass = rootNodeClass;
	}

	public E getRootNode() {
		return mRootNode;
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
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

	@SuppressWarnings("unchecked")
	@Override
	public boolean process(IElement root) throws Throwable {
		if (mRootNodeClass.isAssignableFrom(root.getClass())) {
			if (mRootNode == null) {
				mRootNode = (E) root;
			} else {
				throw new IllegalStateException(
						"root node of type " + mRootNodeClass.getSimpleName() + " was already found");
			}
		}
		return false;
	}

}
