/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.observers;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;

/**
 * Access to models in Ultimate is managed through observers. UltimateCore
 * expects tools to provide at least one observer that will be executed by
 * UltimateCore.
 * 
 * <p>
 * Note: Implementers should not implement this interface directly, but rather one of
 * it descendants.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface IObserver {

	/**
	 * Before an observer is executed on a model, UltimateCore calls
	 * <code>init(...)</code> on the observer. If there are many observers,
	 * <code>init(...)</code> is called on each one. If there are many models,
	 * <code>init(...)</code> is called for each one with increasing
	 * <code>currentModelIndex</code>, e.g. if there are 3 models, an IObserver
	 * lifecycle will be:
	 * <ul>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,0,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,1,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,2,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * </ul>
	 * 
	 * @param modelType
	 *            The model type which is about to be executed
	 * @param currentModelIndex
	 *            The current index of the model that is about to be executed
	 * @param numberOfModels
	 *            The total number of models that will be executed by this
	 *            observer
	 * @throws Throwable
	 *             because plugins can fail any way they want during
	 *             {@link #init()} and the core will (try to) handle it.
	 */
	void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable;

	/**
	 * After an observer has finished executing on a model (or chosen to ignore
	 * it), UlimateCore calls finish() on the observer.
	 * 
	 * @throws Throwable
	 *             because plugins can fail any way they want during
	 *             {@link #finish()} and the core will (try to) handle it.
	 */
	void finish() throws Throwable;

	/**
	 * UltimateCore uses this method to determine if a plugin has changed a
	 * model at all.
	 * 
	 * @return true iff this observer has changed a model in any way, false iff
	 *         not.
	 */
	boolean performedChanges();

}
