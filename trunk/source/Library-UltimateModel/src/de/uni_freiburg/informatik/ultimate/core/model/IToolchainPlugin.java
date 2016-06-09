/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.model;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * @see {@link IUltimatePlugin}
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface IToolchainPlugin extends IUltimatePlugin {

	/**
	 * Ultimate provides every {@link IToolchainPlugin} with an
	 * {@link IToolchainStorage} object. You can store your own service or
	 * storage in this object. It will persist over the lifetime of a toolchain
	 * (i.e. until the next toolchain is run or if the controller explicitly
	 * clears it).
	 * 
	 * @param storage
	 *            Ultimate will provide the toolchain storage object here. This
	 *            object will never be null.
	 */
	void setToolchainStorage(IToolchainStorage storage);

	/**
	 * Through {@link IUltimateServiceProvider} you have access to all services
	 * that Ultimate provides (e.g. ResultReporting, Backtranslation, Logging,
	 * ...).
	 * 
	 * The services can be found in the namespace
	 * de.uni_freiburg.informatik.ultimate.core.model.services.
	 * 
	 * @param services
	 *            An instance of {@link IUltimateServiceProvider}. This instance
	 *            will never be null.
	 */
	void setServices(IUltimateServiceProvider services);

	/**
	 * {@link UltimateCore} will call this method according to the
	 * UltimatePlugin lifecycle (once before it is used in a toolchain).
	 * 
	 * Note that this is called <b>BEFORE</b>
	 * {@link #setServices(IUltimateServiceProvider)} and
	 * {@link #setToolchainStorage(IToolchainStorage)}.
	 */
	void init();

	/**
	 * {@link UltimateCore} will call this method once after {@link IToolchainPlugin}
	 * has been processed completely and before starting the next plugin in the
	 * toolchain.
	 */
	void finish();

}
